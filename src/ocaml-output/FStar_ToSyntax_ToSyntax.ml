open Prims
<<<<<<< HEAD
let desugar_disjunctive_pattern :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.branch Prims.list
  =
=======
let (desugar_disjunctive_pattern
  :FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
       FStar_Pervasives_Native.option ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
         FStar_Syntax_Syntax.branch Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat  -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
<<<<<<< HEAD
  
let trans_aqual :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___200_62  ->
    match uu___200_62 with
=======
let (trans_aqual
  :FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
     FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)=
  fun uu___204_62  ->
    match uu___204_62 with
>>>>>>> taramana_pointers_with_codes_modifies
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____67 -> FStar_Pervasives_Native.None
<<<<<<< HEAD
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
=======
let (trans_qual
  :FStar_Range.range ->
     FStar_Ident.lident FStar_Pervasives_Native.option ->
       FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___205_83  ->
        match uu___205_83 with
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
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("The 'default' qualifier on effects is no longer supported",
                   r))
        | FStar_Parser_AST.Inline  ->
            FStar_Exn.raise (FStar_Errors.Error ("Unsupported qualifier", r))
        | FStar_Parser_AST.Visible  ->
            FStar_Exn.raise (FStar_Errors.Error ("Unsupported qualifier", r))
<<<<<<< HEAD
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___202_91  ->
    match uu___202_91 with
=======
let (trans_pragma :FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma)=
  fun uu___206_91  ->
    match uu___206_91 with
>>>>>>> taramana_pointers_with_codes_modifies
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
<<<<<<< HEAD
  
let as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___203_101  ->
    match uu___203_101 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____104 -> FStar_Pervasives_Native.None
  
=======
let (as_imp
  :FStar_Parser_AST.imp ->
     FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)=
  fun uu___207_101  ->
    match uu___207_101 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____104 -> FStar_Pervasives_Native.None
>>>>>>> taramana_pointers_with_codes_modifies
let arg_withimp_e :
  'Auu____111 .
    FStar_Parser_AST.imp ->
      'Auu____111 ->
        ('Auu____111,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
<<<<<<< HEAD
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
=======
          FStar_Pervasives_Native.tuple2=
  fun imp  -> fun t  -> (t, (as_imp imp))
>>>>>>> taramana_pointers_with_codes_modifies
let arg_withimp_t :
  'Auu____134 .
    FStar_Parser_AST.imp ->
      'Auu____134 ->
        ('Auu____134,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2=
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____151 -> (t, FStar_Pervasives_Native.None)
<<<<<<< HEAD
  
let contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool =
=======
let (contains_binder :FStar_Parser_AST.binder Prims.list -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____167 -> true
            | uu____172 -> false))
<<<<<<< HEAD
  
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
=======
let rec (unparen :FStar_Parser_AST.term -> FStar_Parser_AST.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____178 -> t
<<<<<<< HEAD
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
=======
let (tm_type_z :FStar_Range.range -> FStar_Parser_AST.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    let uu____183 =
      let uu____184 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____184  in
    FStar_Parser_AST.mk_term uu____183 r FStar_Parser_AST.Kind
<<<<<<< HEAD
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
=======
let (tm_type :FStar_Range.range -> FStar_Parser_AST.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun r  ->
    let uu____189 =
      let uu____190 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____190  in
    FStar_Parser_AST.mk_term uu____189 r FStar_Parser_AST.Kind
<<<<<<< HEAD
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
=======
let rec (is_comp_type
  :FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____200 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____206) ->
          let uu____219 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____219 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____225,uu____226) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____229,uu____230) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____235,t1) -> is_comp_type env t1
      | uu____237 -> false
<<<<<<< HEAD
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
=======
let (unit_ty :FStar_Parser_AST.term)=
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let (compile_op_lid
  :Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____250 =
          let uu____253 =
            let uu____254 =
              let uu____259 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____259, r)  in
            FStar_Ident.mk_ident uu____254  in
          [uu____253]  in
        FStar_All.pipe_right uu____250 FStar_Ident.lid_of_ids
<<<<<<< HEAD
  
=======
>>>>>>> taramana_pointers_with_codes_modifies
let op_as_term :
  'Auu____272 .
    FStar_ToSyntax_Env.env ->
      Prims.int ->
        'Auu____272 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option=
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____300 =
              let uu____301 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____301 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____300  in
          let fallback uu____307 =
            match FStar_Ident.text_of_id op with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.Delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.Delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.Delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.Delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.Delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.Delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.Delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.Delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.Delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.Delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.Delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.Delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "@" ->
                let uu____310 = FStar_Options.ml_ish ()  in
                if uu____310
                then
                  r FStar_Parser_Const.list_append_lid
                    FStar_Syntax_Syntax.Delta_equational
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.Delta_equational
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.Delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | uu____314 -> FStar_Pervasives_Native.None  in
          let uu____315 =
            let uu____322 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_ToSyntax_Env.try_lookup_lid env uu____322  in
          match uu____315 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____334 -> fallback ()
<<<<<<< HEAD
  
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
=======
let (sort_ftv :FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun ftv  ->
    let uu____351 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____351
<<<<<<< HEAD
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
=======
let rec (free_type_vars_b
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.binder ->
       (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____390 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____394 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____394 with | (env1,uu____406) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____409,term) ->
          let uu____411 = free_type_vars env term  in (env, uu____411)
      | FStar_Parser_AST.TAnnotated (id,uu____417) ->
          let uu____418 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____418 with | (env1,uu____430) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
<<<<<<< HEAD
          let uu____434 = free_type_vars env t  in (env, uu____434)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
=======
          let uu____434 = free_type_vars env t in (env, uu____434)
and (free_type_vars
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      let uu____441 =
        let uu____442 = unparen t  in uu____442.FStar_Parser_AST.tm  in
      match uu____441 with
      | FStar_Parser_AST.Labeled uu____445 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____455 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____455 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____468 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____475 -> []
      | FStar_Parser_AST.Uvar uu____476 -> []
      | FStar_Parser_AST.Var uu____477 -> []
      | FStar_Parser_AST.Projector uu____478 -> []
      | FStar_Parser_AST.Discrim uu____483 -> []
      | FStar_Parser_AST.Name uu____484 -> []
      | FStar_Parser_AST.Assign (uu____485,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____488) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____494) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____499,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____515,ts) ->
          FStar_List.collect
            (fun uu____536  ->
               match uu____536 with | (t1,uu____544) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____545,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____553) ->
          let uu____554 = free_type_vars env t1  in
          let uu____557 = free_type_vars env t2  in
          FStar_List.append uu____554 uu____557
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____562 = free_type_vars_b env b  in
          (match uu____562 with
           | (env1,f) ->
               let uu____577 = free_type_vars env1 t1  in
               FStar_List.append f uu____577)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____586 =
            FStar_List.fold_left
              (fun uu____606  ->
                 fun binder  ->
                   match uu____606 with
                   | (env1,free) ->
                       let uu____626 = free_type_vars_b env1 binder  in
                       (match uu____626 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____586 with
           | (env1,free) ->
               let uu____657 = free_type_vars env1 body  in
               FStar_List.append free uu____657)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____666 =
            FStar_List.fold_left
              (fun uu____686  ->
                 fun binder  ->
                   match uu____686 with
                   | (env1,free) ->
                       let uu____706 = free_type_vars_b env1 binder  in
                       (match uu____706 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____666 with
           | (env1,free) ->
               let uu____737 = free_type_vars env1 body  in
               FStar_List.append free uu____737)
      | FStar_Parser_AST.Project (t1,uu____741) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____745 -> []
      | FStar_Parser_AST.Let uu____752 -> []
      | FStar_Parser_AST.LetOpen uu____765 -> []
      | FStar_Parser_AST.If uu____770 -> []
      | FStar_Parser_AST.QForall uu____777 -> []
      | FStar_Parser_AST.QExists uu____790 -> []
      | FStar_Parser_AST.Record uu____803 -> []
      | FStar_Parser_AST.Match uu____816 -> []
      | FStar_Parser_AST.TryWith uu____831 -> []
      | FStar_Parser_AST.Bind uu____846 -> []
      | FStar_Parser_AST.Seq uu____853 -> []
<<<<<<< HEAD

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
=======
let (head_and_args
  :FStar_Parser_AST.term ->
     (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                              FStar_Pervasives_Native.tuple2 Prims.list)
       FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t  ->
    let rec aux args t1 =
      let uu____901 =
        let uu____902 = unparen t1  in uu____902.FStar_Parser_AST.tm  in
      match uu____901 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____944 -> (t1, args)  in
    aux [] t
<<<<<<< HEAD
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
=======
let (close
  :FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      let ftv =
        let uu____966 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____966  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____984 =
                     let uu____985 =
                       let uu____990 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____990)  in
                     FStar_Parser_AST.TAnnotated uu____985  in
                   FStar_Parser_AST.mk_binder uu____984 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
<<<<<<< HEAD
  
let close_fun :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
=======
let (close_fun
  :FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1005 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1005  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1023 =
                     let uu____1024 =
                       let uu____1029 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1029)  in
                     FStar_Parser_AST.TAnnotated uu____1024  in
                   FStar_Parser_AST.mk_binder uu____1023
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1031 =
             let uu____1032 = unparen t  in uu____1032.FStar_Parser_AST.tm
              in
           match uu____1031 with
           | FStar_Parser_AST.Product uu____1033 -> t
           | uu____1040 ->
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
<<<<<<< HEAD
  
let rec uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2
  =
=======
let rec (uncurry
  :FStar_Parser_AST.binder Prims.list ->
     FStar_Parser_AST.term ->
       (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1074 -> (bs, t)
<<<<<<< HEAD
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
=======
let rec (is_var_pattern :FStar_Parser_AST.pattern -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1081,uu____1082) -> true
    | FStar_Parser_AST.PatVar (uu____1087,uu____1088) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1094) -> is_var_pattern p1
    | uu____1095 -> false
<<<<<<< HEAD
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
=======
let rec (is_app_pattern :FStar_Parser_AST.pattern -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1101) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1102;
           FStar_Parser_AST.prange = uu____1103;_},uu____1104)
        -> true
    | uu____1115 -> false
<<<<<<< HEAD
  
let replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern =
=======
let (replace_unit_pattern
  :FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1120 -> p
<<<<<<< HEAD
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
=======
let rec (destruct_app_pattern
  :FStar_ToSyntax_Env.env ->
     Prims.bool ->
       FStar_Parser_AST.pattern ->
         ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
>>>>>>> taramana_pointers_with_codes_modifies
                                                                    Prims.list,
           FStar_Parser_AST.term FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple3)=
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1163 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1163 with
             | (name,args,uu____1194) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1220);
               FStar_Parser_AST.prange = uu____1221;_},args)
            when is_top_level1 ->
            let uu____1231 =
              let uu____1236 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____1236  in
            (uu____1231, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1246);
               FStar_Parser_AST.prange = uu____1247;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1265 -> failwith "Not an app pattern"
<<<<<<< HEAD
  
let rec gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
=======
let rec (gather_pattern_bound_vars_maybe_top
  :FStar_Ident.ident FStar_Util.set ->
     FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____1305 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1306,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1309 -> acc
      | FStar_Parser_AST.PatTvar uu____1310 -> acc
      | FStar_Parser_AST.PatOp uu____1317 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1325) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1334) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1349 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1349
      | FStar_Parser_AST.PatAscribed (pat,uu____1357) ->
          gather_pattern_bound_vars_maybe_top acc pat
<<<<<<< HEAD
  
let gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
=======
let (gather_pattern_bound_vars
  :FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)=
>>>>>>> taramana_pointers_with_codes_modifies
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
<<<<<<< HEAD
           then (Prims.parse_int "0")
           else (Prims.parse_int "1"))
      (fun uu____1372  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
=======
           then Prims.parse_int "0"
           else Prims.parse_int "1") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
>>>>>>> taramana_pointers_with_codes_modifies
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
<<<<<<< HEAD
  FStar_Pervasives_Native.tuple2 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1399 -> false
  
let __proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1429 -> false
  
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
  fun uu___204_1457  ->
    match uu___204_1457 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1464 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
          FStar_Pervasives_Native.tuple2
  =
=======
  FStar_Pervasives_Native.tuple2
let (uu___is_LocalBinder :bnd -> Prims.bool)=
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1397 -> false
let (__proj__LocalBinder__item___0
  :bnd ->
     (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder :bnd -> Prims.bool)=
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1427 -> false
let (__proj__LetBinder__item___0
  :bnd ->
     (FStar_Ident.lident,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let (binder_of_bnd
  :bnd ->
     (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2)=
  fun uu___208_1455  ->
    match uu___208_1455 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1462 -> failwith "Impossible"
let (as_binder
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
       (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2 ->
         (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
           FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun imp  ->
      fun uu___209_1490  ->
        match uu___209_1490 with
        | (FStar_Pervasives_Native.None ,k) ->
<<<<<<< HEAD
            let uu____1508 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1508, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1513 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____1513 with
             | (env1,a1) ->
                 (((let uu___226_1533 = a1  in
=======
            let uu____1506 = FStar_Syntax_Syntax.null_binder k in
            (uu____1506, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1511 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1511 with
             | (env1,a1) ->
                 (((let uu___230_1531 = a1 in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___230_1531.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___230_1531.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
<<<<<<< HEAD
let mk_lb :
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____1553  ->
    match uu____1553 with
=======
let (mk_lb
  :((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                            FStar_Syntax_Syntax.syntax)
     FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding)=
  fun uu____1551  ->
    match uu____1551 with
>>>>>>> taramana_pointers_with_codes_modifies
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
<<<<<<< HEAD
  
let no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
=======
let (no_annot_abs
  :FStar_Syntax_Syntax.binders ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
let (mk_ref_read
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun tm  ->
    let tm' =
      let uu____1604 =
        let uu____1619 =
          let uu____1620 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
<<<<<<< HEAD
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1622  in
        let uu____1623 =
          let uu____1632 =
            let uu____1639 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1639)  in
          [uu____1632]  in
        (uu____1621, uu____1623)  in
      FStar_Syntax_Syntax.Tm_app uu____1606  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
=======
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1620 in
        let uu____1621 =
          let uu____1630 =
            let uu____1637 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1637) in
          [uu____1630] in
        (uu____1619, uu____1621) in
      FStar_Syntax_Syntax.Tm_app uu____1604 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun tm  ->
    let tm' =
      let uu____1671 =
        let uu____1686 =
          let uu____1687 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
<<<<<<< HEAD
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1689  in
        let uu____1690 =
          let uu____1699 =
            let uu____1706 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1706)  in
          [uu____1699]  in
        (uu____1688, uu____1690)  in
      FStar_Syntax_Syntax.Tm_app uu____1673  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
=======
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1687 in
        let uu____1688 =
          let uu____1697 =
            let uu____1704 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1704) in
          [uu____1697] in
        (uu____1686, uu____1688) in
      FStar_Syntax_Syntax.Tm_app uu____1671 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let (mk_ref_assign
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       FStar_Range.range ->
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____1750 =
            let uu____1765 =
              let uu____1766 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
<<<<<<< HEAD
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1768  in
            let uu____1769 =
              let uu____1778 =
                let uu____1785 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1785)  in
              let uu____1788 =
                let uu____1797 =
                  let uu____1804 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1804)  in
                [uu____1797]  in
              uu____1778 :: uu____1788  in
            (uu____1767, uu____1769)  in
          FStar_Syntax_Syntax.Tm_app uu____1752  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___206_1836  ->
    match uu___206_1836 with
=======
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____1766 in
            let uu____1767 =
              let uu____1776 =
                let uu____1783 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____1783) in
              let uu____1786 =
                let uu____1795 =
                  let uu____1802 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____1802) in
                [uu____1795] in
              uu____1776 :: uu____1786 in
            (uu____1765, uu____1767) in
          FStar_Syntax_Syntax.Tm_app uu____1750 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let (is_special_effect_combinator :Prims.string -> Prims.bool)=
  fun uu___210_1834  ->
    match uu___210_1834 with
>>>>>>> taramana_pointers_with_codes_modifies
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
<<<<<<< HEAD
    | uu____1837 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
=======
    | uu____1835 -> false
let rec (sum_to_universe
  :FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
<<<<<<< HEAD
        (let uu____1847 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1847)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1864 =
      let uu____1865 = unparen t  in uu____1865.FStar_Parser_AST.tm  in
    match uu____1864 with
    | FStar_Parser_AST.Wild  ->
        let uu____1870 =
          let uu____1871 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1871  in
        FStar_Util.Inr uu____1870
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1882)) ->
        let n1 = FStar_Util.int_of_string repr  in
=======
        (let uu____1845 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1845)
let (int_to_universe :Prims.int -> FStar_Syntax_Syntax.universe)=
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec (desugar_maybe_non_constant_universe
  :FStar_Parser_AST.term ->
     (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)=
  fun t  ->
    let uu____1862 =
      let uu____1863 = unparen t in uu____1863.FStar_Parser_AST.tm in
    match uu____1862 with
    | FStar_Parser_AST.Wild  ->
        let uu____1868 =
          let uu____1869 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1869 in
        FStar_Util.Inr uu____1868
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1880)) ->
        let n1 = FStar_Util.int_of_string repr in
>>>>>>> taramana_pointers_with_codes_modifies
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Exn.raise
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
<<<<<<< HEAD
             let uu____1948 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1948
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1959 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1959
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1970 =
               let uu____1971 =
                 let uu____1976 =
                   let uu____1977 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1977
                    in
                 (uu____1976, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1971  in
             FStar_Exn.raise uu____1970)
    | FStar_Parser_AST.App uu____1982 ->
        let rec aux t1 univargs =
          let uu____2012 =
            let uu____2013 = unparen t1  in uu____2013.FStar_Parser_AST.tm
             in
          match uu____2012 with
          | FStar_Parser_AST.App (t2,targ,uu____2020) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
=======
             let uu____1946 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1946
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1957 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1957
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1968 =
               let uu____1969 =
                 let uu____1974 =
                   let uu____1975 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1975 in
                 (uu____1974, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1969 in
             FStar_Exn.raise uu____1968)
    | FStar_Parser_AST.App uu____1980 ->
        let rec aux t1 univargs =
          let uu____2010 =
            let uu____2011 = unparen t1 in uu____2011.FStar_Parser_AST.tm in
          match uu____2010 with
          | FStar_Parser_AST.App (t2,targ,uu____2018) ->
              let uarg = desugar_maybe_non_constant_universe targ in
>>>>>>> taramana_pointers_with_codes_modifies
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___211_2042  ->
                     match uu___211_2042 with
                     | FStar_Util.Inr uu____2047 -> true
                     | uu____2048 -> false) univargs
              then
                let uu____2053 =
                  let uu____2054 =
                    FStar_List.map
                      (fun uu___212_2063  ->
                         match uu___212_2063 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
<<<<<<< HEAD
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2056  in
                FStar_Util.Inr uu____2055
=======
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2054 in
                FStar_Util.Inr uu____2053
>>>>>>> taramana_pointers_with_codes_modifies
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___213_2080  ->
                        match uu___213_2080 with
                        | FStar_Util.Inl n1 -> n1
<<<<<<< HEAD
                        | FStar_Util.Inr uu____2088 -> failwith "impossible")
                     univargs
                    in
                 let uu____2089 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2089)
          | uu____2095 ->
              let uu____2096 =
                let uu____2097 =
                  let uu____2102 =
                    let uu____2103 =
                      let uu____2104 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____2104 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____2103  in
                  (uu____2102, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____2097  in
              FStar_Exn.raise uu____2096
           in
        aux t []
    | uu____2113 ->
        let uu____2114 =
          let uu____2115 =
            let uu____2120 =
              let uu____2121 =
                let uu____2122 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____2122 " in universe context"  in
              Prims.strcat "Unexpected term " uu____2121  in
            (uu____2120, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____2115  in
        FStar_Exn.raise uu____2114
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
=======
                        | FStar_Util.Inr uu____2086 -> failwith "impossible")
                     univargs in
                 let uu____2087 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2087)
          | uu____2093 ->
              let uu____2094 =
                let uu____2095 =
                  let uu____2100 =
                    let uu____2101 =
                      let uu____2102 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____2102 " in universe context" in
                    Prims.strcat "Unexpected term " uu____2101 in
                  (uu____2100, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____2095 in
              FStar_Exn.raise uu____2094 in
        aux t []
    | uu____2111 ->
        let uu____2112 =
          let uu____2113 =
            let uu____2118 =
              let uu____2119 =
                let uu____2120 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____2120 " in universe context" in
              Prims.strcat "Unexpected term " uu____2119 in
            (uu____2118, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____2113 in
        FStar_Exn.raise uu____2112
let rec (desugar_universe
  :FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
<<<<<<< HEAD
  
let check_fields :
  'Auu____2146 .
=======
let check_fields :
  'Auu____2144 .
>>>>>>> taramana_pointers_with_codes_modifies
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2144) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc=
  fun env  ->
    fun fields  ->
      fun rg  ->
<<<<<<< HEAD
        let uu____2171 = FStar_List.hd fields  in
        match uu____2171 with
        | (f,uu____2181) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2191 =
                match uu____2191 with
                | (f',uu____2197) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2199 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record
                         in
                      if uu____2199
=======
        let uu____2169 = FStar_List.hd fields in
        match uu____2169 with
        | (f,uu____2179) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
              let check_field uu____2189 =
                match uu____2189 with
                | (f',uu____2195) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2197 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record in
                      if uu____2197
>>>>>>> taramana_pointers_with_codes_modifies
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
<<<<<<< HEAD
                             f'.FStar_Ident.str
                            in
                         FStar_Exn.raise (FStar_Errors.Error (msg, rg)))))
                 in
              (let uu____2203 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2203);
              (match () with | () -> record)))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3
  =
=======
                             f'.FStar_Ident.str in
                         FStar_Exn.raise (FStar_Errors.Error (msg, rg))))) in
              (let uu____2201 = FStar_List.tl fields in
               FStar_List.iter check_field uu____2201);
              (match () with | () -> record)))
let rec (desugar_data_pat
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.pattern ->
       Prims.bool ->
         (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
           FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2417 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2424 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2425 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2427,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
<<<<<<< HEAD
                        fun uu____2469  ->
                          match uu____2469 with
                          | (p3,uu____2479) ->
                              let uu____2480 = pat_vars p3  in
                              FStar_Util.set_union out uu____2480)
                     FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
=======
                        fun uu____2467  ->
                          match uu____2467 with
                          | (p3,uu____2477) ->
                              let uu____2478 = pat_vars p3 in
                              FStar_Util.set_union out uu____2478)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
>>>>>>> taramana_pointers_with_codes_modifies
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2482) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2483) -> ()
         | (true ,uu____2490) ->
             FStar_Exn.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____2525 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
<<<<<<< HEAD
                       x.FStar_Ident.idText))
              in
           match uu____2527 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2541 ->
               let uu____2544 = push_bv_maybe_mut e x  in
               (match uu____2544 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
=======
                       x.FStar_Ident.idText)) in
           match uu____2525 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2539 ->
               let uu____2542 = push_bv_maybe_mut e x in
               (match uu____2542 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
>>>>>>> taramana_pointers_with_codes_modifies
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2606 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2622 =
                 let uu____2623 =
                   let uu____2624 =
                     let uu____2631 =
                       let uu____2632 =
                         let uu____2637 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
<<<<<<< HEAD
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2639, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2634  in
                     (uu____2633, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2626  in
=======
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____2637, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2632 in
                     (uu____2631, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2624 in
>>>>>>> taramana_pointers_with_codes_modifies
                 {
                   FStar_Parser_AST.pat = uu____2623;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
<<<<<<< HEAD
                 }  in
               aux loc env1 uu____2624
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2644 = aux loc env1 p2  in
               (match uu____2644 with
=======
                 } in
               aux loc env1 uu____2622
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2642 = aux loc env1 p2 in
               (match uu____2642 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____2677 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
<<<<<<< HEAD
                            let uu____2687 = close_fun env1 t  in
                            desugar_term env1 uu____2687  in
=======
                            let uu____2685 = close_fun env1 t in
                            desugar_term env1 uu____2685 in
>>>>>>> taramana_pointers_with_codes_modifies
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2687 -> true)
                           then
<<<<<<< HEAD
                             (let uu____2690 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____2691 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____2692 =
                                FStar_Syntax_Print.term_to_string t1  in
=======
                             (let uu____2688 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2689 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2690 =
                                FStar_Syntax_Print.term_to_string t1 in
>>>>>>> taramana_pointers_with_codes_modifies
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____2688 uu____2689 uu____2690)
                           else ();
                           LocalBinder
<<<<<<< HEAD
                             (((let uu___227_2695 = x  in
=======
                             (((let uu___231_2693 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___231_2693.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___231_2693.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq))
                       in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
<<<<<<< HEAD
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2699 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
=======
                   FStar_Syntax_Syntax.tun in
               let uu____2697 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
>>>>>>> taramana_pointers_with_codes_modifies
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2697, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
<<<<<<< HEAD
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2710 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
=======
                   FStar_Syntax_Syntax.tun in
               let uu____2708 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
>>>>>>> taramana_pointers_with_codes_modifies
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2708, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
<<<<<<< HEAD
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2731 = resolvex loc env1 x  in
               (match uu____2731 with
=======
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2729 = resolvex loc env1 x in
               (match uu____2729 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (loc1,env2,xbv) ->
                    let uu____2751 =
                      FStar_All.pipe_left pos
<<<<<<< HEAD
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2753, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2774 = resolvex loc env1 x  in
               (match uu____2774 with
=======
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2751, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2772 = resolvex loc env1 x in
               (match uu____2772 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (loc1,env2,xbv) ->
                    let uu____2794 =
                      FStar_All.pipe_left pos
<<<<<<< HEAD
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2796, imp))
=======
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2794, imp))
>>>>>>> taramana_pointers_with_codes_modifies
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
<<<<<<< HEAD
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2808 =
=======
                   FStar_Syntax_Syntax.tun in
               let uu____2806 =
>>>>>>> taramana_pointers_with_codes_modifies
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2806, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2830;_},args)
               ->
               let uu____2836 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2877  ->
                        match uu____2877 with
                        | (loc1,env2,args1) ->
<<<<<<< HEAD
                            let uu____2927 = aux loc1 env2 arg  in
                            (match uu____2927 with
                             | (loc2,env3,uu____2956,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2838 with
=======
                            let uu____2925 = aux loc1 env2 arg in
                            (match uu____2925 with
                             | (loc2,env3,uu____2954,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2836 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
<<<<<<< HEAD
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____3026 =
=======
                        FStar_Syntax_Syntax.tun in
                    let uu____3024 =
>>>>>>> taramana_pointers_with_codes_modifies
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3024, false))
           | FStar_Parser_AST.PatApp uu____3041 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3063 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3096  ->
                        match uu____3096 with
                        | (loc1,env2,pats1) ->
<<<<<<< HEAD
                            let uu____3130 = aux loc1 env2 pat  in
                            (match uu____3130 with
                             | (loc2,env3,uu____3155,pat1,uu____3157) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3065 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3200 =
                        let uu____3203 =
                          let uu____3208 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3208  in
                        let uu____3209 =
                          let uu____3210 =
                            let uu____3223 =
=======
                            let uu____3128 = aux loc1 env2 pat in
                            (match uu____3128 with
                             | (loc2,env3,uu____3153,pat1,uu____3155) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3063 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3198 =
                        let uu____3201 =
                          let uu____3206 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3206 in
                        let uu____3207 =
                          let uu____3208 =
                            let uu____3221 =
>>>>>>> taramana_pointers_with_codes_modifies
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3223, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3210  in
                        FStar_All.pipe_left uu____3203 uu____3209  in
=======
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3221, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3208 in
                        FStar_All.pipe_left uu____3201 uu____3207 in
>>>>>>> taramana_pointers_with_codes_modifies
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
<<<<<<< HEAD
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3255 =
                               let uu____3256 =
                                 let uu____3269 =
=======
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3253 =
                               let uu____3254 =
                                 let uu____3267 =
>>>>>>> taramana_pointers_with_codes_modifies
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3269, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3256  in
                             FStar_All.pipe_left (pos_r r) uu____3255) pats1
                        uu____3200
                       in
=======
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3267, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3254 in
                             FStar_All.pipe_left (pos_r r) uu____3253) pats1
                        uu____3198 in
>>>>>>> taramana_pointers_with_codes_modifies
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
               let uu____3311 =
                 FStar_List.fold_left
                   (fun uu____3351  ->
                      fun p2  ->
                        match uu____3351 with
                        | (loc1,env2,pats) ->
<<<<<<< HEAD
                            let uu____3402 = aux loc1 env2 p2  in
                            (match uu____3402 with
                             | (loc2,env3,uu____3431,pat,uu____3433) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3313 with
=======
                            let uu____3400 = aux loc1 env2 p2 in
                            (match uu____3400 with
                             | (loc2,env3,uu____3429,pat,uu____3431) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3311 with
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____3528 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____3528 with
                     | (constr,uu____3550) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3553 -> failwith "impossible"  in
=======
                          p1.FStar_Parser_AST.prange in
                    let uu____3526 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3526 with
                     | (constr,uu____3548) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3551 -> failwith "impossible" in
>>>>>>> taramana_pointers_with_codes_modifies
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
<<<<<<< HEAD
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3555 =
=======
                             FStar_Syntax_Syntax.tun in
                         let uu____3553 =
>>>>>>> taramana_pointers_with_codes_modifies
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3553, false)))
           | FStar_Parser_AST.PatRecord [] ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
<<<<<<< HEAD
                      (fun uu____3626  ->
                         match uu____3626 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
=======
                      (fun uu____3624  ->
                         match uu____3624 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
>>>>>>> taramana_pointers_with_codes_modifies
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3654  ->
                         match uu____3654 with
                         | (f,uu____3660) ->
                             let uu____3661 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3687  ->
                                       match uu____3687 with
                                       | (g,uu____3693) ->
                                           f.FStar_Ident.idText =
<<<<<<< HEAD
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3663 with
=======
                                             g.FStar_Ident.idText)) in
                             (match uu____3661 with
>>>>>>> taramana_pointers_with_codes_modifies
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
<<<<<<< HEAD
                              | FStar_Pervasives_Native.Some (uu____3700,p2)
                                  -> p2)))
                  in
=======
                              | FStar_Pervasives_Native.Some (uu____3698,p2)
                                  -> p2))) in
>>>>>>> taramana_pointers_with_codes_modifies
               let app =
                 let uu____3705 =
                   let uu____3706 =
                     let uu____3713 =
                       let uu____3714 =
                         let uu____3715 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
<<<<<<< HEAD
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3717  in
                       FStar_Parser_AST.mk_pattern uu____3716
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3715, args)  in
                   FStar_Parser_AST.PatApp uu____3708  in
                 FStar_Parser_AST.mk_pattern uu____3707
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3720 = aux loc env1 app  in
               (match uu____3720 with
                | (env2,e,b,p2,uu____3749) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3777 =
                            let uu____3778 =
                              let uu____3791 =
                                let uu___228_3792 = fv  in
                                let uu____3793 =
                                  let uu____3796 =
                                    let uu____3797 =
                                      let uu____3804 =
=======
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3715 in
                       FStar_Parser_AST.mk_pattern uu____3714
                         p1.FStar_Parser_AST.prange in
                     (uu____3713, args) in
                   FStar_Parser_AST.PatApp uu____3706 in
                 FStar_Parser_AST.mk_pattern uu____3705
                   p1.FStar_Parser_AST.prange in
               let uu____3718 = aux loc env1 app in
               (match uu____3718 with
                | (env2,e,b,p2,uu____3747) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3775 =
                            let uu____3776 =
                              let uu____3789 =
                                let uu___232_3790 = fv in
                                let uu____3791 =
                                  let uu____3794 =
                                    let uu____3795 =
                                      let uu____3802 =
>>>>>>> taramana_pointers_with_codes_modifies
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
<<<<<<< HEAD
                                        uu____3804)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3797
                                     in
                                  FStar_Pervasives_Native.Some uu____3796  in
=======
                                        uu____3802) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3795 in
                                  FStar_Pervasives_Native.Some uu____3794 in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___232_3790.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
<<<<<<< HEAD
                                    (uu___228_3792.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3793
                                }  in
                              (uu____3791, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3778  in
                          FStar_All.pipe_left pos uu____3777
                      | uu____3831 -> p2  in
                    (env2, e, b, p3, false))
            in
=======
                                    (uu___232_3790.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3791
                                } in
                              (uu____3789, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____3776 in
                          FStar_All.pipe_left pos uu____3775
                      | uu____3829 -> p2 in
                    (env2, e, b, p3, false)) in
>>>>>>> taramana_pointers_with_codes_modifies
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
<<<<<<< HEAD
               let uu____3878 = aux loc env1 p2  in
               (match uu____3878 with
                | (loc1,env2,var,p3,uu____3905) ->
                    let uu____3910 =
=======
               let uu____3876 = aux loc env1 p2 in
               (match uu____3876 with
                | (loc1,env2,var,p3,uu____3903) ->
                    let uu____3908 =
>>>>>>> taramana_pointers_with_codes_modifies
                      FStar_List.fold_left
                        (fun uu____3940  ->
                           fun p4  ->
                             match uu____3940 with
                             | (loc2,env3,ps1) ->
<<<<<<< HEAD
                                 let uu____3975 = aux loc2 env3 p4  in
                                 (match uu____3975 with
                                  | (loc3,env4,uu____4000,p5,uu____4002) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3910 with
=======
                                 let uu____3973 = aux loc2 env3 p4 in
                                 (match uu____3973 with
                                  | (loc3,env4,uu____3998,p5,uu____4000) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____3908 with
>>>>>>> taramana_pointers_with_codes_modifies
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
<<<<<<< HEAD
           | uu____4053 ->
               let uu____4054 = aux loc env1 p1  in
               (match uu____4054 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4094 = aux_maybe_or env p  in
         match uu____4094 with
         | (env1,b,pats) ->
             ((let uu____4125 =
                 FStar_List.map check_linear_pattern_variables pats  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4125);
              (env1, b, pats)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3
  =
=======
           | uu____4051 ->
               let uu____4052 = aux loc env1 p1 in
               (match uu____4052 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4092 = aux_maybe_or env p in
         match uu____4092 with
         | (env1,b,pats) ->
             ((let uu____4123 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4123);
              (env1, b, pats)))
and (desugar_binding_pat_maybe_top
  :Prims.bool ->
     FStar_ToSyntax_Env.env ->
       FStar_Parser_AST.pattern ->
         Prims.bool ->
           (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
             FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
<<<<<<< HEAD
            let uu____4160 =
              let uu____4161 =
                let uu____4166 = FStar_ToSyntax_Env.qualify env x  in
                (uu____4166, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4161  in
            (env, uu____4160, [])  in
=======
            let uu____4158 =
              let uu____4159 =
                let uu____4164 = FStar_ToSyntax_Env.qualify env x in
                (uu____4164, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4159 in
            (env, uu____4158, []) in
>>>>>>> taramana_pointers_with_codes_modifies
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4184 =
                  let uu____4185 =
                    let uu____4190 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
<<<<<<< HEAD
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4192, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4187  in
                mklet uu____4186
            | FStar_Parser_AST.PatVar (x,uu____4194) -> mklet x
=======
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4190, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4185 in
                mklet uu____4184
            | FStar_Parser_AST.PatVar (x,uu____4192) -> mklet x
>>>>>>> taramana_pointers_with_codes_modifies
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4198);
                   FStar_Parser_AST.prange = uu____4199;_},t)
                ->
<<<<<<< HEAD
                let uu____4207 =
                  let uu____4208 =
                    let uu____4213 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____4214 = desugar_term env t  in
                    (uu____4213, uu____4214)  in
                  LetBinder uu____4208  in
                (env, uu____4207, [])
            | uu____4217 ->
=======
                let uu____4205 =
                  let uu____4206 =
                    let uu____4211 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4212 = desugar_term env t in
                    (uu____4211, uu____4212) in
                  LetBinder uu____4206 in
                (env, uu____4205, [])
            | uu____4215 ->
>>>>>>> taramana_pointers_with_codes_modifies
                FStar_Exn.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
<<<<<<< HEAD
            (let uu____4227 = desugar_data_pat env p is_mut  in
             match uu____4227 with
=======
            (let uu____4225 = desugar_data_pat env p is_mut in
             match uu____4225 with
>>>>>>> taramana_pointers_with_codes_modifies
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4254;
                       FStar_Syntax_Syntax.p = uu____4255;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
<<<<<<< HEAD
                         uu____4262;
                       FStar_Syntax_Syntax.p = uu____4263;_}::[] -> []
                   | uu____4268 -> p1  in
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
  fun uu____4275  ->
    fun env  ->
      fun pat  ->
        let uu____4278 = desugar_data_pat env pat false  in
        match uu____4278 with | (env1,uu____4294,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
=======
                         uu____4260;
                       FStar_Syntax_Syntax.p = uu____4261;_}::[] -> []
                   | uu____4266 -> p1 in
                 (env1, binder, p2))
and (desugar_binding_pat
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.pattern ->
       (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
         FStar_Pervasives_Native.tuple3)=
  fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and (desugar_match_pat_maybe_top
  :Prims.bool ->
     FStar_ToSyntax_Env.env ->
       FStar_Parser_AST.pattern ->
         (env_t,FStar_Syntax_Syntax.pat Prims.list)
           FStar_Pervasives_Native.tuple2)=
  fun uu____4273  ->
    fun env  ->
      fun pat  ->
        let uu____4276 = desugar_data_pat env pat false in
        match uu____4276 with | (env1,uu____4292,pat1) -> (env1, pat1)
and (desugar_match_pat
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.pattern ->
       (env_t,FStar_Syntax_Syntax.pat Prims.list)
         FStar_Pervasives_Native.tuple2)=
  fun env  -> fun p  -> desugar_match_pat_maybe_top false env p
and (desugar_term
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e
<<<<<<< HEAD

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
=======
and (desugar_typ
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e
<<<<<<< HEAD

and desugar_machine_integer :
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
=======
and (desugar_machine_integer
  :FStar_ToSyntax_Env.env ->
     Prims.string ->
       (FStar_Const.signedness,FStar_Const.width)
         FStar_Pervasives_Native.tuple2 ->
         FStar_Range.range ->
           FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun repr  ->
      fun uu____4310  ->
        fun range  ->
          match uu____4310 with
          | (signedness,width) ->
<<<<<<< HEAD
              let uu____4322 = FStar_Const.bounds signedness width  in
              (match uu____4322 with
               | (lower,upper) ->
                   let value =
                     let uu____4332 = FStar_Util.ensure_decimal repr  in
                     FStar_Util.int_of_string uu____4332  in
=======
              let uu____4320 = FStar_Const.bounds signedness width in
              (match uu____4320 with
               | (lower,upper) ->
                   let value =
                     let uu____4330 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____4330 in
>>>>>>> taramana_pointers_with_codes_modifies
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
                      (let uu____4333 =
                         let uu____4334 =
                           let uu____4339 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
<<<<<<< HEAD
                               tnm
                              in
                           (uu____4341, range)  in
                         FStar_Errors.Error uu____4336  in
                       FStar_Exn.raise uu____4335)
=======
                               tnm in
                           (uu____4339, range) in
                         FStar_Errors.Error uu____4334 in
                       FStar_Exn.raise uu____4333)
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                       let uu____4349 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid  in
                       match uu____4349 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4359)
=======
                       let uu____4347 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____4347 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4357)
>>>>>>> taramana_pointers_with_codes_modifies
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range
                                   in
                                let private_fv =
                                  let uu____4367 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta
                                     in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
<<<<<<< HEAD
                                    uu____4369 fv.FStar_Syntax_Syntax.fv_qual
                                   in
                                let uu___229_4370 = intro_term  in
=======
                                    uu____4367 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___233_4368 = intro_term in
>>>>>>> taramana_pointers_with_codes_modifies
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___233_4368.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___233_4368.FStar_Syntax_Syntax.vars)
                                }
                            | uu____4369 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____4376 =
                             let uu____4377 =
                               let uu____4382 =
                                 FStar_Util.format1
                                   "Unexpected numeric literal.  Restart F* to load %s."
<<<<<<< HEAD
                                   tnm
                                  in
                               (uu____4384, range)  in
                             FStar_Errors.Error uu____4379  in
                           FStar_Exn.raise uu____4378
                        in
=======
                                   tnm in
                               (uu____4382, range) in
                             FStar_Errors.Error uu____4377 in
                           FStar_Exn.raise uu____4376 in
>>>>>>> taramana_pointers_with_codes_modifies
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
<<<<<<< HEAD
                         FStar_Pervasives_Native.None range
                        in
                     let uu____4400 =
                       let uu____4403 =
                         let uu____4404 =
                           let uu____4419 =
                             let uu____4428 =
                               let uu____4435 =
                                 FStar_Syntax_Syntax.as_implicit false  in
                               (repr1, uu____4435)  in
                             [uu____4428]  in
                           (lid1, uu____4419)  in
                         FStar_Syntax_Syntax.Tm_app uu____4404  in
                       FStar_Syntax_Syntax.mk uu____4403  in
                     uu____4400 FStar_Pervasives_Native.None range)))

and desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
=======
                         FStar_Pervasives_Native.None range in
                     let uu____4398 =
                       let uu____4401 =
                         let uu____4402 =
                           let uu____4417 =
                             let uu____4426 =
                               let uu____4433 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____4433) in
                             [uu____4426] in
                           (lid1, uu____4417) in
                         FStar_Syntax_Syntax.Tm_app uu____4402 in
                       FStar_Syntax_Syntax.mk uu____4401 in
                     uu____4398 FStar_Pervasives_Native.None range)))
and (desugar_name
  :(FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
     (FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
       -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____4472 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
<<<<<<< HEAD
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____4474 with
=======
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4472 with
>>>>>>> taramana_pointers_with_codes_modifies
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
<<<<<<< HEAD
                  let uu____4489 =
                    let uu____4490 =
                      let uu____4497 = mk_ref_read tm1  in
                      (uu____4497,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____4490  in
                  FStar_All.pipe_left mk1 uu____4489
                else tm1

and desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4513 =
          let uu____4514 = unparen t  in uu____4514.FStar_Parser_AST.tm  in
        match uu____4513 with
=======
                  let uu____4487 =
                    let uu____4488 =
                      let uu____4495 = mk_ref_read tm1 in
                      (uu____4495,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4488 in
                  FStar_All.pipe_left mk1 uu____4487
                else tm1
and (desugar_attributes
  :env_t ->
     FStar_Parser_AST.term Prims.list ->
       FStar_Syntax_Syntax.cflags Prims.list)=
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4511 =
          let uu____4512 = unparen t in uu____4512.FStar_Parser_AST.tm in
        match uu____4511 with
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4513; FStar_Ident.ident = uu____4514;
              FStar_Ident.nsstr = uu____4515; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
<<<<<<< HEAD
        | uu____4520 ->
            let uu____4521 =
              let uu____4522 =
                let uu____4527 =
                  let uu____4528 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____4528  in
                (uu____4527, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____4522  in
            FStar_Exn.raise uu____4521
         in
      FStar_List.map desugar_attribute cattributes

and desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
=======
        | uu____4518 ->
            let uu____4519 =
              let uu____4520 =
                let uu____4525 =
                  let uu____4526 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4526 in
                (uu____4525, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4520 in
            FStar_Exn.raise uu____4519 in
      FStar_List.map desugar_attribute cattributes
and (desugar_term_maybe_top
  :Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let setpos e =
<<<<<<< HEAD
          let uu___230_4548 = e  in
=======
          let uu___234_4546 = e in
>>>>>>> taramana_pointers_with_codes_modifies
          {
            FStar_Syntax_Syntax.n = (uu___234_4546.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
<<<<<<< HEAD
              (uu___230_4548.FStar_Syntax_Syntax.vars)
          }  in
        let uu____4551 =
          let uu____4552 = unparen top  in uu____4552.FStar_Parser_AST.tm  in
        match uu____4551 with
=======
              (uu___234_4546.FStar_Syntax_Syntax.vars)
          } in
        let uu____4549 =
          let uu____4550 = unparen top in uu____4550.FStar_Parser_AST.tm in
        match uu____4549 with
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4551 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4602::uu____4603::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4607 =
                 op_as_term env (Prims.parse_int "2")
<<<<<<< HEAD
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4609 FStar_Option.isNone)
=======
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4607 FStar_Option.isNone)
>>>>>>> taramana_pointers_with_codes_modifies
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4620;_},t1::t2::[])
                  ->
<<<<<<< HEAD
                  let uu____4627 = flatten1 t1  in
                  FStar_List.append uu____4627 [t2]
              | uu____4630 -> [t]  in
            let targs =
              let uu____4634 =
                let uu____4637 = unparen top  in flatten1 uu____4637  in
              FStar_All.pipe_right uu____4634
                (FStar_List.map
                   (fun t  ->
                      let uu____4645 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4645))
               in
            let uu____4646 =
              let uu____4651 =
=======
                  let uu____4625 = flatten1 t1 in
                  FStar_List.append uu____4625 [t2]
              | uu____4628 -> [t] in
            let targs =
              let uu____4632 =
                let uu____4635 = unparen top in flatten1 uu____4635 in
              FStar_All.pipe_right uu____4632
                (FStar_List.map
                   (fun t  ->
                      let uu____4643 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____4643)) in
            let uu____4644 =
              let uu____4649 =
>>>>>>> taramana_pointers_with_codes_modifies
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
<<<<<<< HEAD
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4651
               in
            (match uu____4646 with
             | (tup,uu____4657) ->
=======
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4649 in
            (match uu____4644 with
             | (tup,uu____4655) ->
>>>>>>> taramana_pointers_with_codes_modifies
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4659 =
              let uu____4662 =
                FStar_ToSyntax_Env.fail_or2
<<<<<<< HEAD
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4664  in
            FStar_All.pipe_left setpos uu____4661
=======
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____4662 in
            FStar_All.pipe_left setpos uu____4659
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Uvar u ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4682 =
              op_as_term env (FStar_List.length args)
<<<<<<< HEAD
                top.FStar_Parser_AST.range s
               in
            (match uu____4684 with
=======
                top.FStar_Parser_AST.range s in
            (match uu____4682 with
>>>>>>> taramana_pointers_with_codes_modifies
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise
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
<<<<<<< HEAD
                             let uu____4716 = desugar_term env t  in
                             (uu____4716, FStar_Pervasives_Native.None)))
                      in
=======
                             let uu____4714 = desugar_term env t in
                             (uu____4714, FStar_Pervasives_Native.None))) in
>>>>>>> taramana_pointers_with_codes_modifies
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4728)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
<<<<<<< HEAD
            let uu____4745 =
              let uu___231_4746 = top  in
              let uu____4747 =
                let uu____4748 =
                  let uu____4755 =
                    let uu___232_4756 = top  in
                    let uu____4757 =
                      let uu____4758 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4758  in
=======
            let uu____4743 =
              let uu___235_4744 = top in
              let uu____4745 =
                let uu____4746 =
                  let uu____4753 =
                    let uu___236_4754 = top in
                    let uu____4755 =
                      let uu____4756 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4756 in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Parser_AST.tm = uu____4755;
                      FStar_Parser_AST.range =
                        (uu___236_4754.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
<<<<<<< HEAD
                        (uu___232_4756.FStar_Parser_AST.level)
                    }  in
                  (uu____4755, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4748  in
=======
                        (uu___236_4754.FStar_Parser_AST.level)
                    } in
                  (uu____4753, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4746 in
>>>>>>> taramana_pointers_with_codes_modifies
              {
                FStar_Parser_AST.tm = uu____4745;
                FStar_Parser_AST.range =
                  (uu___235_4744.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
<<<<<<< HEAD
                  (uu___231_4746.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4745
        | FStar_Parser_AST.Construct (n1,(a,uu____4761)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____4776 =
              let uu___233_4777 = top  in
              let uu____4778 =
                let uu____4779 =
                  let uu____4786 =
                    let uu___234_4787 = top  in
                    let uu____4788 =
                      let uu____4789 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4789  in
=======
                  (uu___235_4744.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4743
        | FStar_Parser_AST.Construct (n1,(a,uu____4759)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____4774 =
              let uu___237_4775 = top in
              let uu____4776 =
                let uu____4777 =
                  let uu____4784 =
                    let uu___238_4785 = top in
                    let uu____4786 =
                      let uu____4787 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4787 in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Parser_AST.tm = uu____4786;
                      FStar_Parser_AST.range =
                        (uu___238_4785.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
<<<<<<< HEAD
                        (uu___234_4787.FStar_Parser_AST.level)
                    }  in
                  (uu____4786, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4779  in
=======
                        (uu___238_4785.FStar_Parser_AST.level)
                    } in
                  (uu____4784, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4777 in
>>>>>>> taramana_pointers_with_codes_modifies
              {
                FStar_Parser_AST.tm = uu____4776;
                FStar_Parser_AST.range =
                  (uu___237_4775.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
<<<<<<< HEAD
                  (uu___233_4777.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4776
        | FStar_Parser_AST.Construct (n1,(a,uu____4792)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4807 =
              let uu___235_4808 = top  in
              let uu____4809 =
                let uu____4810 =
                  let uu____4817 =
                    let uu___236_4818 = top  in
                    let uu____4819 =
                      let uu____4820 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4820  in
=======
                  (uu___237_4775.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4774
        | FStar_Parser_AST.Construct (n1,(a,uu____4790)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4805 =
              let uu___239_4806 = top in
              let uu____4807 =
                let uu____4808 =
                  let uu____4815 =
                    let uu___240_4816 = top in
                    let uu____4817 =
                      let uu____4818 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4818 in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Parser_AST.tm = uu____4817;
                      FStar_Parser_AST.range =
                        (uu___240_4816.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
<<<<<<< HEAD
                        (uu___236_4818.FStar_Parser_AST.level)
                    }  in
                  (uu____4817, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4810  in
=======
                        (uu___240_4816.FStar_Parser_AST.level)
                    } in
                  (uu____4815, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4808 in
>>>>>>> taramana_pointers_with_codes_modifies
              {
                FStar_Parser_AST.tm = uu____4807;
                FStar_Parser_AST.range =
                  (uu___239_4806.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
<<<<<<< HEAD
                  (uu___235_4808.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4807
=======
                  (uu___239_4806.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4805
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4819; FStar_Ident.ident = uu____4820;
              FStar_Ident.nsstr = uu____4821; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4824; FStar_Ident.ident = uu____4825;
              FStar_Ident.nsstr = uu____4826; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4829; FStar_Ident.ident = uu____4830;
               FStar_Ident.nsstr = uu____4831; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
<<<<<<< HEAD
            let uu____4851 =
              let uu____4852 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____4852  in
            mk1 uu____4851
=======
            let uu____4849 =
              let uu____4850 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____4850 in
            mk1 uu____4849
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4851; FStar_Ident.ident = uu____4852;
              FStar_Ident.nsstr = uu____4853; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4856; FStar_Ident.ident = uu____4857;
              FStar_Ident.nsstr = uu____4858; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4861; FStar_Ident.ident = uu____4862;
              FStar_Ident.nsstr = uu____4863; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____4868;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
<<<<<<< HEAD
             (let uu____4872 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____4872 with
=======
             (let uu____4870 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____4870 with
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____4875 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
<<<<<<< HEAD
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____4877))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____4881 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____4881 with
=======
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____4875))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____4879 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____4879 with
>>>>>>> taramana_pointers_with_codes_modifies
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    FStar_Exn.raise
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
<<<<<<< HEAD
                let uu____4908 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____4908 with
                | FStar_Pervasives_Native.Some uu____4917 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____4922 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____4922 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____4936 -> FStar_Pervasives_Native.None)
                 in
=======
                let uu____4906 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____4906 with
                | FStar_Pervasives_Native.Some uu____4915 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____4920 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____4920 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____4934 -> FStar_Pervasives_Native.None) in
>>>>>>> taramana_pointers_with_codes_modifies
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____4947 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
<<<<<<< HEAD
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____4949
              | uu____4950 ->
                  let uu____4957 =
                    let uu____4958 =
                      let uu____4963 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str
                         in
                      (uu____4963, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____4958  in
                  FStar_Exn.raise uu____4957))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____4966 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____4966 with
=======
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____4947
              | uu____4948 ->
                  let uu____4955 =
                    let uu____4956 =
                      let uu____4961 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____4961, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____4956 in
                  FStar_Exn.raise uu____4955))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____4964 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____4964 with
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Pervasives_Native.None  ->
                  let uu____4967 =
                    let uu____4968 =
                      let uu____4973 =
                        FStar_Util.format1 "Data constructor %s not found"
<<<<<<< HEAD
                          lid.FStar_Ident.str
                         in
                      (uu____4975, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____4970  in
                  FStar_Exn.raise uu____4969
              | uu____4976 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____4995 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____4995 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____4999 =
                    let uu____5006 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____5006, true)  in
                  (match uu____4999 with
=======
                          lid.FStar_Ident.str in
                      (uu____4973, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____4968 in
                  FStar_Exn.raise uu____4967
              | uu____4974 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____4993 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____4993 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____4997 =
                    let uu____5004 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5004, true) in
                  (match uu____4997 with
>>>>>>> taramana_pointers_with_codes_modifies
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5019 ->
                            let uu____5026 =
                              FStar_Util.take
<<<<<<< HEAD
                                (fun uu____5052  ->
                                   match uu____5052 with
                                   | (uu____5057,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____5028 with
=======
                                (fun uu____5050  ->
                                   match uu____5050 with
                                   | (uu____5055,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5026 with
>>>>>>> taramana_pointers_with_codes_modifies
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
                                     (fun uu____5119  ->
                                        match uu____5119 with
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
<<<<<<< HEAD
                    let uu____5164 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____5164 with
=======
                    let uu____5162 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5162 with
>>>>>>> taramana_pointers_with_codes_modifies
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5165 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position")
                     in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5172 =
              FStar_List.fold_left
                (fun uu____5217  ->
                   fun b  ->
                     match uu____5217 with
                     | (env1,tparams,typs) ->
<<<<<<< HEAD
                         let uu____5276 = desugar_binder env1 b  in
                         (match uu____5276 with
=======
                         let uu____5274 = desugar_binder env1 b in
                         (match uu____5274 with
>>>>>>> taramana_pointers_with_codes_modifies
                          | (xopt,t1) ->
                              let uu____5303 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5312 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
<<<<<<< HEAD
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5314)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____5305 with
                               | (env2,x) ->
                                   let uu____5334 =
                                     let uu____5337 =
                                       let uu____5340 =
                                         let uu____5341 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5341
                                          in
                                       [uu____5340]  in
                                     FStar_List.append typs uu____5337  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___237_5367 = x  in
=======
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5312)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5303 with
                               | (env2,x) ->
                                   let uu____5332 =
                                     let uu____5335 =
                                       let uu____5338 =
                                         let uu____5339 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5339 in
                                       [uu____5338] in
                                     FStar_List.append typs uu____5335 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___241_5365 = x in
>>>>>>> taramana_pointers_with_codes_modifies
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___241_5365.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___241_5365.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5332)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
<<<<<<< HEAD
                      FStar_Pervasives_Native.None])
               in
            (match uu____5174 with
             | (env1,uu____5391,targs) ->
                 let uu____5413 =
                   let uu____5418 =
=======
                      FStar_Pervasives_Native.None]) in
            (match uu____5172 with
             | (env1,uu____5389,targs) ->
                 let uu____5411 =
                   let uu____5416 =
>>>>>>> taramana_pointers_with_codes_modifies
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
<<<<<<< HEAD
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5418
                    in
                 (match uu____5413 with
                  | (tup,uu____5424) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5435 = uncurry binders t  in
            (match uu____5435 with
=======
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5416 in
                 (match uu____5411 with
                  | (tup,uu____5422) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5433 = uncurry binders t in
            (match uu____5433 with
>>>>>>> taramana_pointers_with_codes_modifies
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___214_5465 =
                   match uu___214_5465 with
                   | [] ->
                       let cod =
<<<<<<< HEAD
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5481 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5481
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5503 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5503 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5518 = desugar_binder env b  in
            (match uu____5518 with
             | (FStar_Pervasives_Native.None ,uu____5525) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5535 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5535 with
                  | ((x,uu____5541),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5548 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5548))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5568 =
=======
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5479 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5479
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5501 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5501 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5516 = desugar_binder env b in
            (match uu____5516 with
             | (FStar_Pervasives_Native.None ,uu____5523) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5533 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5533 with
                  | ((x,uu____5539),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5546 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5546))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5566 =
>>>>>>> taramana_pointers_with_codes_modifies
              FStar_List.fold_left
                (fun uu____5586  ->
                   fun pat  ->
                     match uu____5586 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
<<<<<<< HEAD
                          | FStar_Parser_AST.PatAscribed (uu____5614,t) ->
                              let uu____5616 =
                                let uu____5619 = free_type_vars env1 t  in
                                FStar_List.append uu____5619 ftvs  in
                              (env1, uu____5616)
                          | uu____5624 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5568 with
             | (uu____5629,ftv) ->
                 let ftv1 = sort_ftv ftv  in
=======
                          | FStar_Parser_AST.PatAscribed (uu____5612,t) ->
                              let uu____5614 =
                                let uu____5617 = free_type_vars env1 t in
                                FStar_List.append uu____5617 ftvs in
                              (env1, uu____5614)
                          | uu____5622 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5566 with
             | (uu____5627,ftv) ->
                 let ftv1 = sort_ftv ftv in
>>>>>>> taramana_pointers_with_codes_modifies
                 let binders2 =
                   let uu____5639 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
<<<<<<< HEAD
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____5641 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___211_5682 =
                   match uu___211_5682 with
=======
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5639 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___215_5680 =
                   match uu___215_5680 with
>>>>>>> taramana_pointers_with_codes_modifies
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
<<<<<<< HEAD
                               let uu____5720 =
                                 let uu____5721 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5721
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5720 body1  in
=======
                               let uu____5718 =
                                 let uu____5719 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5719
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5718 body1 in
>>>>>>> taramana_pointers_with_codes_modifies
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5774 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5774
                   | p::rest ->
                       let uu____5785 = desugar_binding_pat env1 p  in
                       (match uu____5785 with
=======
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____5772 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____5772
                   | p::rest ->
                       let uu____5783 = desugar_binding_pat env1 p in
                       (match uu____5783 with
>>>>>>> taramana_pointers_with_codes_modifies
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5807 ->
                                  FStar_Exn.raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
<<<<<<< HEAD
                                         (p.FStar_Parser_AST.prange)))
                               in
                            let uu____5814 =
=======
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____5812 =
>>>>>>> taramana_pointers_with_codes_modifies
                              match b with
                              | LetBinder uu____5845 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____5895) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
<<<<<<< HEAD
                                        let uu____5933 =
                                          let uu____5938 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____5938, p1)  in
=======
                                        let uu____5931 =
                                          let uu____5936 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____5936, p1) in
>>>>>>> taramana_pointers_with_codes_modifies
                                        FStar_Pervasives_Native.Some
                                          uu____5931
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____5972,uu____5973) ->
                                             let tup2 =
                                               let uu____5975 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____5975
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____5979 =
                                                 let uu____5982 =
                                                   let uu____5983 =
                                                     let uu____5998 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
                                                            tup2)
                                                        in
                                                     let uu____6003 =
                                                       let uu____6006 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6007 =
                                                         let uu____6010 =
                                                           let uu____6011 =
=======
                                                            tup2) in
                                                     let uu____6001 =
                                                       let uu____6004 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6005 =
                                                         let uu____6008 =
                                                           let uu____6009 =
>>>>>>> taramana_pointers_with_codes_modifies
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                             uu____6011
                                                            in
                                                         [uu____6010]  in
                                                       uu____6006 ::
                                                         uu____6007
                                                        in
                                                     (uu____6000, uu____6003)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____5985
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5984
                                                  in
                                               uu____5981
=======
                                                             uu____6009 in
                                                         [uu____6008] in
                                                       uu____6004 ::
                                                         uu____6005 in
                                                     (uu____5998, uu____6001) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____5983 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5982 in
                                               uu____5979
>>>>>>> taramana_pointers_with_codes_modifies
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6020 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
<<<<<<< HEAD
                                                 uu____6022
                                                in
=======
                                                 uu____6020 in
>>>>>>> taramana_pointers_with_codes_modifies
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6051,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6053,pats)) ->
                                             let tupn =
                                               let uu____6092 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6092
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6102 =
                                                 let uu____6103 =
                                                   let uu____6118 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
                                                          tupn)
                                                      in
                                                   let uu____6123 =
                                                     let uu____6132 =
                                                       let uu____6141 =
                                                         let uu____6142 =
=======
                                                          tupn) in
                                                   let uu____6121 =
                                                     let uu____6130 =
                                                       let uu____6139 =
                                                         let uu____6140 =
>>>>>>> taramana_pointers_with_codes_modifies
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                           uu____6142
                                                          in
                                                       [uu____6141]  in
                                                     FStar_List.append args
                                                       uu____6132
                                                      in
                                                   (uu____6120, uu____6123)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6105
                                                  in
                                               mk1 uu____6104  in
=======
                                                           uu____6140 in
                                                       [uu____6139] in
                                                     FStar_List.append args
                                                       uu____6130 in
                                                   (uu____6118, uu____6121) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6103 in
                                               mk1 uu____6102 in
>>>>>>> taramana_pointers_with_codes_modifies
                                             let p2 =
                                               let uu____6160 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
<<<<<<< HEAD
                                                 uu____6162
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6197 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5814 with
=======
                                                 uu____6160 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6195 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____5812 with
>>>>>>> taramana_pointers_with_codes_modifies
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6262,uu____6263,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
<<<<<<< HEAD
              let uu____6279 =
                let uu____6280 = unparen e  in uu____6280.FStar_Parser_AST.tm
                 in
              match uu____6279 with
=======
              let uu____6277 =
                let uu____6278 = unparen e in uu____6278.FStar_Parser_AST.tm in
              match uu____6277 with
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
<<<<<<< HEAD
              | uu____6286 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
=======
              | uu____6284 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
>>>>>>> taramana_pointers_with_codes_modifies
            aux [] top
        | FStar_Parser_AST.App uu____6288 ->
            let rec aux args e =
<<<<<<< HEAD
              let uu____6322 =
                let uu____6323 = unparen e  in uu____6323.FStar_Parser_AST.tm
                 in
              match uu____6322 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6336 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6336  in
                  aux (arg :: args) e1
              | uu____6349 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
=======
              let uu____6320 =
                let uu____6321 = unparen e in uu____6321.FStar_Parser_AST.tm in
              match uu____6320 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6334 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6334 in
                  aux (arg :: args) e1
              | uu____6347 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
              let uu____6375 =
                let uu____6376 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
                FStar_Parser_AST.Var uu____6376  in
              FStar_Parser_AST.mk_term uu____6375 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr
               in
            let uu____6377 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term env uu____6377
=======
              let uu____6373 =
                let uu____6374 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6374 in
              FStar_Parser_AST.mk_term uu____6373 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6375 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6375
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6378 =
              let uu____6379 =
                let uu____6386 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
<<<<<<< HEAD
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____6388,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6381  in
            mk1 uu____6380
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____6406 =
              let uu____6411 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____6411 then desugar_typ else desugar_term  in
            uu____6406 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6444 =
              let bindings = (pat, _snd) :: _tl  in
=======
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6386,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6379 in
            mk1 uu____6378
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6404 =
              let uu____6409 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6409 then desugar_typ else desugar_term in
            uu____6404 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6442 =
              let bindings = (pat, _snd) :: _tl in
>>>>>>> taramana_pointers_with_codes_modifies
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6528  ->
                        match uu____6528 with
                        | (p,def) ->
<<<<<<< HEAD
                            let uu____6555 = is_app_pattern p  in
                            if uu____6555
                            then
                              let uu____6574 =
                                destruct_app_pattern env top_level p  in
                              (uu____6574, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6628 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____6628, def1)
                               | uu____6657 ->
=======
                            let uu____6553 = is_app_pattern p in
                            if uu____6553
                            then
                              let uu____6572 =
                                destruct_app_pattern env top_level p in
                              (uu____6572, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6626 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____6626, def1)
                               | uu____6655 ->
>>>>>>> taramana_pointers_with_codes_modifies
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____6681);
                                           FStar_Parser_AST.prange =
                                             uu____6682;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6706 =
                                            let uu____6721 =
                                              let uu____6726 =
                                                FStar_ToSyntax_Env.qualify
<<<<<<< HEAD
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____6728  in
                                            (uu____6723, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (uu____6708, def)
=======
                                                  env id in
                                              FStar_Util.Inr uu____6726 in
                                            (uu____6721, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____6706, def)
>>>>>>> taramana_pointers_with_codes_modifies
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____6773)
                                        ->
                                        if top_level
                                        then
                                          let uu____6796 =
                                            let uu____6811 =
                                              let uu____6816 =
                                                FStar_ToSyntax_Env.qualify
<<<<<<< HEAD
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____6818  in
                                            (uu____6813, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (uu____6798, def)
=======
                                                  env id in
                                              FStar_Util.Inr uu____6816 in
                                            (uu____6811, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____6796, def)
>>>>>>> taramana_pointers_with_codes_modifies
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____6862 ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
<<<<<<< HEAD
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____6883 =
=======
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____6881 =
>>>>>>> taramana_pointers_with_codes_modifies
                FStar_List.fold_left
                  (fun uu____6941  ->
                     fun uu____6942  ->
                       match (uu____6941, uu____6942) with
                       | ((env1,fnames,rec_bindings),((f,uu____7025,uu____7026),uu____7027))
                           ->
                           let uu____7106 =
                             match f with
                             | FStar_Util.Inl x ->
<<<<<<< HEAD
                                 let uu____7134 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____7134 with
                                  | (env2,xx) ->
                                      let uu____7153 =
                                        let uu____7156 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7156 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7153))
=======
                                 let uu____7132 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7132 with
                                  | (env2,xx) ->
                                      let uu____7151 =
                                        let uu____7154 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7154 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7151))
>>>>>>> taramana_pointers_with_codes_modifies
                             | FStar_Util.Inr l ->
                                 let uu____7162 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
<<<<<<< HEAD
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7164, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7108 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____6883 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7290 =
                    match uu____7290 with
                    | ((uu____7313,args,result_t),def) ->
=======
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7162, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7106 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____6881 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7288 =
                    match uu____7288 with
                    | ((uu____7311,args,result_t),def) ->
>>>>>>> taramana_pointers_with_codes_modifies
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
<<<<<<< HEAD
                                let uu____7357 = is_comp_type env1 t  in
                                if uu____7357
=======
                                let uu____7355 = is_comp_type env1 t in
                                if uu____7355
>>>>>>> taramana_pointers_with_codes_modifies
                                then
                                  ((let uu____7357 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
<<<<<<< HEAD
                                              let uu____7369 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7369))
                                       in
                                    match uu____7359 with
=======
                                              let uu____7367 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7367)) in
                                    match uu____7357 with
>>>>>>> taramana_pointers_with_codes_modifies
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7370 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7372 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
<<<<<<< HEAD
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7374))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7372
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7378 =
=======
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7372))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7370
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7376 =
>>>>>>> taramana_pointers_with_codes_modifies
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
<<<<<<< HEAD
                                uu____7378 FStar_Parser_AST.Expr
                           in
=======
                                uu____7376 FStar_Parser_AST.Expr in
>>>>>>> taramana_pointers_with_codes_modifies
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7380 ->
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
                              let uu____7395 =
                                let uu____7396 =
                                  FStar_Syntax_Util.incr_delta_qualifier
<<<<<<< HEAD
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7398
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7397
                           in
=======
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7396
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7395 in
>>>>>>> taramana_pointers_with_codes_modifies
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        mk_lb (lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
<<<<<<< HEAD
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____7432 =
                    let uu____7433 =
                      let uu____7446 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____7446)  in
                    FStar_Syntax_Syntax.Tm_let uu____7433  in
                  FStar_All.pipe_left mk1 uu____7432
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____7477 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____7477 with
=======
                      fnames1 funs in
                  let body1 = desugar_term env' body in
                  let uu____7430 =
                    let uu____7431 =
                      let uu____7444 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7444) in
                    FStar_Syntax_Syntax.Tm_let uu____7431 in
                  FStar_All.pipe_left mk1 uu____7430 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7475 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7475 with
>>>>>>> taramana_pointers_with_codes_modifies
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
<<<<<<< HEAD
                          let uu____7504 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7504
                            FStar_Pervasives_Native.None
                           in
=======
                          let uu____7502 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7502
                            FStar_Pervasives_Native.None in
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                    | LocalBinder (x,uu____7516) ->
                        let body1 = desugar_term env1 t2  in
=======
                    | LocalBinder (x,uu____7514) ->
                        let body1 = desugar_term env1 t2 in
>>>>>>> taramana_pointers_with_codes_modifies
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7517;
                              FStar_Syntax_Syntax.p = uu____7518;_}::[] ->
                              body1
<<<<<<< HEAD
                          | uu____7525 ->
                              let uu____7528 =
                                let uu____7531 =
                                  let uu____7532 =
                                    let uu____7555 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____7556 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____7555, uu____7556)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7532  in
                                FStar_Syntax_Syntax.mk uu____7531  in
                              uu____7528 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____7566 =
                          let uu____7567 =
                            let uu____7580 =
                              let uu____7581 =
                                let uu____7582 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____7582]  in
                              FStar_Syntax_Subst.close uu____7581 body2  in
=======
                          | uu____7523 ->
                              let uu____7526 =
                                let uu____7529 =
                                  let uu____7530 =
                                    let uu____7553 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7554 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7553, uu____7554) in
                                  FStar_Syntax_Syntax.Tm_match uu____7530 in
                                FStar_Syntax_Syntax.mk uu____7529 in
                              uu____7526 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7564 =
                          let uu____7565 =
                            let uu____7578 =
                              let uu____7579 =
                                let uu____7580 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____7580] in
                              FStar_Syntax_Subst.close uu____7579 body2 in
>>>>>>> taramana_pointers_with_codes_modifies
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
<<<<<<< HEAD
                              uu____7580)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____7567  in
                        FStar_All.pipe_left mk1 uu____7566
                     in
=======
                              uu____7578) in
                          FStar_Syntax_Syntax.Tm_let uu____7565 in
                        FStar_All.pipe_left mk1 uu____7564 in
>>>>>>> taramana_pointers_with_codes_modifies
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
<<<<<<< HEAD
                  else tm
               in
            let uu____7608 = is_rec || (is_app_pattern pat)  in
            if uu____7608
=======
                  else tm in
            let uu____7606 = is_rec || (is_app_pattern pat) in
            if uu____7606
>>>>>>> taramana_pointers_with_codes_modifies
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____7615 =
                let uu____7616 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
<<<<<<< HEAD
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____7618  in
              mk1 uu____7617  in
            let uu____7619 =
              let uu____7620 =
                let uu____7643 =
                  let uu____7646 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____7646
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____7667 =
                  let uu____7682 =
                    let uu____7695 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____7698 = desugar_term env t2  in
                    (uu____7695, FStar_Pervasives_Native.None, uu____7698)
                     in
                  let uu____7707 =
                    let uu____7722 =
                      let uu____7735 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____7738 = desugar_term env t3  in
                      (uu____7735, FStar_Pervasives_Native.None, uu____7738)
                       in
                    [uu____7722]  in
                  uu____7682 :: uu____7707  in
                (uu____7643, uu____7667)  in
              FStar_Syntax_Syntax.Tm_match uu____7620  in
            mk1 uu____7619
=======
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____7616 in
              mk1 uu____7615 in
            let uu____7617 =
              let uu____7618 =
                let uu____7641 =
                  let uu____7644 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____7644
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____7665 =
                  let uu____7680 =
                    let uu____7693 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____7696 = desugar_term env t2 in
                    (uu____7693, FStar_Pervasives_Native.None, uu____7696) in
                  let uu____7705 =
                    let uu____7720 =
                      let uu____7733 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____7736 = desugar_term env t3 in
                      (uu____7733, FStar_Pervasives_Native.None, uu____7736) in
                    [uu____7720] in
                  uu____7680 :: uu____7705 in
                (uu____7641, uu____7665) in
              FStar_Syntax_Syntax.Tm_match uu____7618 in
            mk1 uu____7617
>>>>>>> taramana_pointers_with_codes_modifies
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
            let desugar_branch uu____7877 =
              match uu____7877 with
              | (pat,wopt,b) ->
<<<<<<< HEAD
                  let uu____7897 = desugar_match_pat env pat  in
                  (match uu____7897 with
=======
                  let uu____7895 = desugar_match_pat env pat in
                  (match uu____7895 with
>>>>>>> taramana_pointers_with_codes_modifies
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
<<<<<<< HEAD
                             let uu____7918 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____7918
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____7920 =
              let uu____7921 =
                let uu____7944 = desugar_term env e  in
                let uu____7945 = FStar_List.collect desugar_branch branches
                   in
                (uu____7944, uu____7945)  in
              FStar_Syntax_Syntax.Tm_match uu____7921  in
            FStar_All.pipe_left mk1 uu____7920
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____7974 = is_comp_type env t  in
              if uu____7974
              then
                let uu____7981 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____7981
              else
                (let uu____7987 = desugar_term env t  in
                 FStar_Util.Inl uu____7987)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____7993 =
              let uu____7994 =
                let uu____8021 = desugar_term env e  in
                (uu____8021, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____7994  in
            FStar_All.pipe_left mk1 uu____7993
        | FStar_Parser_AST.Record (uu____8046,[]) ->
=======
                             let uu____7916 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____7916 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____7918 =
              let uu____7919 =
                let uu____7942 = desugar_term env e in
                let uu____7943 = FStar_List.collect desugar_branch branches in
                (uu____7942, uu____7943) in
              FStar_Syntax_Syntax.Tm_match uu____7919 in
            FStar_All.pipe_left mk1 uu____7918
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____7972 = is_comp_type env t in
              if uu____7972
              then
                let uu____7979 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____7979
              else
                (let uu____7985 = desugar_term env t in
                 FStar_Util.Inl uu____7985) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____7991 =
              let uu____7992 =
                let uu____8019 = desugar_term env e in
                (uu____8019, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____7992 in
            FStar_All.pipe_left mk1 uu____7991
        | FStar_Parser_AST.Record (uu____8044,[]) ->
>>>>>>> taramana_pointers_with_codes_modifies
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
<<<<<<< HEAD
              let uu____8083 = FStar_List.hd fields  in
              match uu____8083 with | (f,uu____8095) -> f.FStar_Ident.ns  in
=======
              let uu____8081 = FStar_List.hd fields in
              match uu____8081 with | (f,uu____8093) -> f.FStar_Ident.ns in
>>>>>>> taramana_pointers_with_codes_modifies
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8135  ->
                        match uu____8135 with
                        | (g,uu____8141) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8147,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8161 =
                         let uu____8162 =
                           let uu____8167 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
<<<<<<< HEAD
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____8169, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____8164  in
                       FStar_Exn.raise uu____8163
=======
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8167, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8162 in
                       FStar_Exn.raise uu____8161
>>>>>>> taramana_pointers_with_codes_modifies
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
                  let uu____8175 =
                    let uu____8186 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8217  ->
                              match uu____8217 with
                              | (f,uu____8227) ->
                                  let uu____8228 =
                                    let uu____8229 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
<<<<<<< HEAD
                                      FStar_Pervasives_Native.snd uu____8231
                                     in
                                  (uu____8230, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8188)  in
                  FStar_Parser_AST.Construct uu____8177
=======
                                      FStar_Pervasives_Native.snd uu____8229 in
                                  (uu____8228, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8186) in
                  FStar_Parser_AST.Construct uu____8175
>>>>>>> taramana_pointers_with_codes_modifies
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
<<<<<<< HEAD
                    let uu____8249 =
                      let uu____8250 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8250  in
                    FStar_Parser_AST.mk_term uu____8249 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
=======
                    let uu____8247 =
                      let uu____8248 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8248 in
                    FStar_Parser_AST.mk_term uu____8247 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
>>>>>>> taramana_pointers_with_codes_modifies
                  let record1 =
                    let uu____8250 =
                      let uu____8263 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8293  ->
                                match uu____8293 with
                                | (f,uu____8303) ->
                                    get_field
<<<<<<< HEAD
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8265)  in
                    FStar_Parser_AST.Record uu____8252  in
=======
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8263) in
                    FStar_Parser_AST.Record uu____8250 in
>>>>>>> taramana_pointers_with_codes_modifies
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
                         FStar_Syntax_Syntax.pos = uu____8331;
                         FStar_Syntax_Syntax.vars = uu____8332;_},args);
                    FStar_Syntax_Syntax.pos = uu____8334;
                    FStar_Syntax_Syntax.vars = uu____8335;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8363 =
                     let uu____8364 =
                       let uu____8379 =
                         let uu____8380 =
                           let uu____8383 =
                             let uu____8384 =
                               let uu____8391 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
<<<<<<< HEAD
                                 uu____8393)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____8386  in
                           FStar_Pervasives_Native.Some uu____8385  in
=======
                                 uu____8391) in
                             FStar_Syntax_Syntax.Record_ctor uu____8384 in
                           FStar_Pervasives_Native.Some uu____8383 in
>>>>>>> taramana_pointers_with_codes_modifies
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
<<<<<<< HEAD
                           FStar_Syntax_Syntax.Delta_constant uu____8382
                          in
                       (uu____8381, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____8366  in
                   FStar_All.pipe_left mk1 uu____8365  in
=======
                           FStar_Syntax_Syntax.Delta_constant uu____8380 in
                       (uu____8379, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8364 in
                   FStar_All.pipe_left mk1 uu____8363 in
>>>>>>> taramana_pointers_with_codes_modifies
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8422 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8426 =
                FStar_ToSyntax_Env.fail_or env
<<<<<<< HEAD
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____8428 with
=======
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8426 with
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                    else FStar_Pervasives_Native.None  in
                  let uu____8447 =
                    let uu____8448 =
                      let uu____8463 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1
                         in
                      let uu____8464 =
                        let uu____8467 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8467]  in
                      (uu____8463, uu____8464)  in
                    FStar_Syntax_Syntax.Tm_app uu____8448  in
                  FStar_All.pipe_left mk1 uu____8447))
        | FStar_Parser_AST.NamedTyp (uu____8472,e) -> desugar_term env e
=======
                    else FStar_Pervasives_Native.None in
                  let uu____8445 =
                    let uu____8446 =
                      let uu____8461 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____8462 =
                        let uu____8465 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____8465] in
                      (uu____8461, uu____8462) in
                    FStar_Syntax_Syntax.Tm_app uu____8446 in
                  FStar_All.pipe_left mk1 uu____8445))
        | FStar_Parser_AST.NamedTyp (uu____8470,e) -> desugar_term env e
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____8473 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8474 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8475,uu____8476,uu____8477) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____8490,uu____8491,uu____8492) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____8505,uu____8506,uu____8507) ->
            failwith "Not implemented yet"
<<<<<<< HEAD

and not_ascribed : FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8523 -> false
    | uu____8532 -> true

and is_synth_by_tactic :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
=======
and (not_ascribed :FStar_Parser_AST.term -> Prims.bool)=
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8521 -> false
    | uu____8530 -> true
and (is_synth_by_tactic
  :FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
<<<<<<< HEAD
          let uu____8538 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid  in
          (match uu____8538 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8542 -> false

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term,FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
=======
          let uu____8536 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid in
          (match uu____8536 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8540 -> false
and (desugar_args
  :FStar_ToSyntax_Env.env ->
     (FStar_Parser_AST.term,FStar_Parser_AST.imp)
       FStar_Pervasives_Native.tuple2 Prims.list ->
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple2 Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____8577  ->
              match uu____8577 with
              | (a,imp) ->
<<<<<<< HEAD
                  let uu____8592 = desugar_term env a  in
                  arg_withimp_e imp uu____8592))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = FStar_Exn.raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____8611 =
          match uu____8611 with
          | (t1,uu____8617) ->
              let uu____8618 =
                let uu____8619 = unparen t1  in
                uu____8619.FStar_Parser_AST.tm  in
              (match uu____8618 with
               | FStar_Parser_AST.Requires uu____8620 -> true
               | uu____8627 -> false)
           in
        let is_ensures uu____8635 =
          match uu____8635 with
          | (t1,uu____8641) ->
              let uu____8642 =
                let uu____8643 = unparen t1  in
                uu____8643.FStar_Parser_AST.tm  in
              (match uu____8642 with
               | FStar_Parser_AST.Ensures uu____8644 -> true
               | uu____8651 -> false)
           in
        let is_app head1 uu____8662 =
          match uu____8662 with
          | (t1,uu____8668) ->
              let uu____8669 =
                let uu____8670 = unparen t1  in
                uu____8670.FStar_Parser_AST.tm  in
              (match uu____8669 with
=======
                  let uu____8590 = desugar_term env a in
                  arg_withimp_e imp uu____8590))
and (desugar_comp
  :FStar_Range.range ->
     FStar_ToSyntax_Env.env ->
       FStar_Parser_AST.term ->
         FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)=
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = FStar_Exn.raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____8609 =
          match uu____8609 with
          | (t1,uu____8615) ->
              let uu____8616 =
                let uu____8617 = unparen t1 in uu____8617.FStar_Parser_AST.tm in
              (match uu____8616 with
               | FStar_Parser_AST.Requires uu____8618 -> true
               | uu____8625 -> false) in
        let is_ensures uu____8633 =
          match uu____8633 with
          | (t1,uu____8639) ->
              let uu____8640 =
                let uu____8641 = unparen t1 in uu____8641.FStar_Parser_AST.tm in
              (match uu____8640 with
               | FStar_Parser_AST.Ensures uu____8642 -> true
               | uu____8649 -> false) in
        let is_app head1 uu____8660 =
          match uu____8660 with
          | (t1,uu____8666) ->
              let uu____8667 =
                let uu____8668 = unparen t1 in uu____8668.FStar_Parser_AST.tm in
              (match uu____8667 with
>>>>>>> taramana_pointers_with_codes_modifies
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____8670;
                      FStar_Parser_AST.level = uu____8671;_},uu____8672,uu____8673)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
<<<<<<< HEAD
               | uu____8676 -> false)
           in
        let is_smt_pat uu____8684 =
          match uu____8684 with
          | (t1,uu____8690) ->
              let uu____8691 =
                let uu____8692 = unparen t1  in
                uu____8692.FStar_Parser_AST.tm  in
              (match uu____8691 with
=======
               | uu____8674 -> false) in
        let is_smt_pat uu____8682 =
          match uu____8682 with
          | (t1,uu____8688) ->
              let uu____8689 =
                let uu____8690 = unparen t1 in uu____8690.FStar_Parser_AST.tm in
              (match uu____8689 with
>>>>>>> taramana_pointers_with_codes_modifies
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____8693);
                             FStar_Parser_AST.range = uu____8694;
                             FStar_Parser_AST.level = uu____8695;_},uu____8696)::uu____8697::[])
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
                             FStar_Parser_AST.range = uu____8736;
                             FStar_Parser_AST.level = uu____8737;_},uu____8738)::uu____8739::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
<<<<<<< HEAD
               | uu____8766 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____8794 = head_and_args t1  in
          match uu____8794 with
=======
               | uu____8764 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____8792 = head_and_args t1 in
          match uu____8792 with
>>>>>>> taramana_pointers_with_codes_modifies
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
                         FStar_Exn.raise
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
                   let uu____9201 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
<<<<<<< HEAD
                          env) l
                      in
                   (uu____9203, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9231 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____9231
=======
                          env) l in
                   (uu____9201, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9229 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9229
>>>>>>> taramana_pointers_with_codes_modifies
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
<<<<<<< HEAD
                   (let uu____9249 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____9249
=======
                   (let uu____9247 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9247
>>>>>>> taramana_pointers_with_codes_modifies
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
               | uu____9285 ->
                   let default_effect =
<<<<<<< HEAD
                     let uu____9289 = FStar_Options.ml_ish ()  in
                     if uu____9289
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9292 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____9292
=======
                     let uu____9287 = FStar_Options.ml_ish () in
                     if uu____9287
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9290 =
                           FStar_Options.warn_default_effects () in
                         if uu____9290
>>>>>>> taramana_pointers_with_codes_modifies
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
<<<<<<< HEAD
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____9316 = pre_process_comp_typ t  in
        match uu____9316 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9365 =
                  let uu____9366 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9366
                   in
                fail uu____9365)
             else ();
             (let is_universe uu____9375 =
                match uu____9375 with
                | (uu____9380,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____9382 = FStar_Util.take is_universe args  in
              match uu____9382 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9441  ->
                         match uu____9441 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____9448 =
                    let uu____9463 = FStar_List.hd args1  in
                    let uu____9472 = FStar_List.tl args1  in
                    (uu____9463, uu____9472)  in
                  (match uu____9448 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____9527 =
                         let is_decrease uu____9563 =
                           match uu____9563 with
                           | (t1,uu____9573) ->
=======
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9314 = pre_process_comp_typ t in
        match uu____9314 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9363 =
                  let uu____9364 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9364 in
                fail uu____9363)
             else ();
             (let is_universe uu____9373 =
                match uu____9373 with
                | (uu____9378,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9380 = FStar_Util.take is_universe args in
              match uu____9380 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9439  ->
                         match uu____9439 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9446 =
                    let uu____9461 = FStar_List.hd args1 in
                    let uu____9470 = FStar_List.tl args1 in
                    (uu____9461, uu____9470) in
                  (match uu____9446 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____9525 =
                         let is_decrease uu____9561 =
                           match uu____9561 with
                           | (t1,uu____9571) ->
>>>>>>> taramana_pointers_with_codes_modifies
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____9581;
                                       FStar_Syntax_Syntax.vars = uu____9582;_},uu____9583::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
<<<<<<< HEAD
                                | uu____9616 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____9527 with
=======
                                | uu____9614 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____9525 with
>>>>>>> taramana_pointers_with_codes_modifies
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____9728  ->
                                      match uu____9728 with
                                      | (t1,uu____9738) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____9747,(arg,uu____9749)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
<<<<<<< HEAD
                                           | uu____9780 -> failwith "impos")))
                               in
=======
                                           | uu____9778 -> failwith "impos"))) in
>>>>>>> taramana_pointers_with_codes_modifies
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
<<<<<<< HEAD
                                | uu____9794 -> false  in
=======
                                | uu____9792 -> false in
>>>>>>> taramana_pointers_with_codes_modifies
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
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
                                           | uu____9942 -> pat  in
                                         let uu____9943 =
                                           let uu____9954 =
                                             let uu____9965 =
                                               let uu____9974 =
=======
                                           | uu____9940 -> pat in
                                         let uu____9941 =
                                           let uu____9952 =
                                             let uu____9963 =
                                               let uu____9972 =
>>>>>>> taramana_pointers_with_codes_modifies
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
<<<<<<< HEAD
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____9974, aq)  in
                                             [uu____9965]  in
                                           ens :: uu____9954  in
                                         req :: uu____9943
                                     | uu____10015 -> rest2
                                   else rest2  in
=======
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____9972, aq) in
                                             [uu____9963] in
                                           ens :: uu____9952 in
                                         req :: uu____9941
                                     | uu____10013 -> rest2
                                   else rest2 in
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD

and desugar_formula :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
=======
and (desugar_formula
  :env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
<<<<<<< HEAD
        | uu____10037 -> FStar_Pervasives_Native.None  in
=======
        | uu____10035 -> FStar_Pervasives_Native.None in
>>>>>>> taramana_pointers_with_codes_modifies
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
<<<<<<< HEAD
        let uu___238_10054 = t  in
=======
        let uu___242_10052 = t in
>>>>>>> taramana_pointers_with_codes_modifies
        {
          FStar_Syntax_Syntax.n = (uu___242_10052.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
<<<<<<< HEAD
            (uu___238_10054.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___239_10088 = b  in
=======
            (uu___242_10052.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___243_10086 = b in
>>>>>>> taramana_pointers_with_codes_modifies
             {
               FStar_Parser_AST.b = (uu___243_10086.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___243_10086.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
<<<<<<< HEAD
                 (uu___239_10088.FStar_Parser_AST.aqual)
             })
           in
=======
                 (uu___243_10086.FStar_Parser_AST.aqual)
             }) in
>>>>>>> taramana_pointers_with_codes_modifies
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
<<<<<<< HEAD
                       let uu____10147 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10147)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10160 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____10160 with
             | (env1,a1) ->
                 let a2 =
                   let uu___240_10170 = a1  in
=======
                       let uu____10145 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10145)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10158 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10158 with
             | (env1,a1) ->
                 let a2 =
                   let uu___244_10168 = a1 in
>>>>>>> taramana_pointers_with_codes_modifies
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___244_10168.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___244_10168.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10190 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
<<<<<<< HEAD
                   let uu____10206 =
                     let uu____10209 =
                       let uu____10210 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____10210]  in
                     no_annot_abs uu____10209 body2  in
                   FStar_All.pipe_left setpos uu____10206  in
                 let uu____10215 =
                   let uu____10216 =
                     let uu____10231 =
=======
                   let uu____10204 =
                     let uu____10207 =
                       let uu____10208 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10208] in
                     no_annot_abs uu____10207 body2 in
                   FStar_All.pipe_left setpos uu____10204 in
                 let uu____10213 =
                   let uu____10214 =
                     let uu____10229 =
>>>>>>> taramana_pointers_with_codes_modifies
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
<<<<<<< HEAD
                         FStar_Pervasives_Native.None
                        in
                     let uu____10232 =
                       let uu____10235 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____10235]  in
                     (uu____10231, uu____10232)  in
                   FStar_Syntax_Syntax.Tm_app uu____10216  in
                 FStar_All.pipe_left mk1 uu____10215)
        | uu____10240 -> failwith "impossible"  in
=======
                         FStar_Pervasives_Native.None in
                     let uu____10230 =
                       let uu____10233 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10233] in
                     (uu____10229, uu____10230) in
                   FStar_Syntax_Syntax.Tm_app uu____10214 in
                 FStar_All.pipe_left mk1 uu____10213)
        | uu____10238 -> failwith "impossible" in
>>>>>>> taramana_pointers_with_codes_modifies
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
<<<<<<< HEAD
              let uu____10312 = q (rest, pats, body)  in
              let uu____10319 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____10312 uu____10319
                FStar_Parser_AST.Formula
               in
            let uu____10320 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____10320 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10329 -> failwith "impossible"  in
      let uu____10332 =
        let uu____10333 = unparen f  in uu____10333.FStar_Parser_AST.tm  in
      match uu____10332 with
=======
              let uu____10310 = q (rest, pats, body) in
              let uu____10317 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____10310 uu____10317
                FStar_Parser_AST.Formula in
            let uu____10318 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____10318 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10327 -> failwith "impossible" in
      let uu____10330 =
        let uu____10331 = unparen f in uu____10331.FStar_Parser_AST.tm in
      match uu____10330 with
>>>>>>> taramana_pointers_with_codes_modifies
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____10338,uu____10339) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____10350,uu____10351) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
<<<<<<< HEAD
          let binders = _1 :: _2 :: _3  in
          let uu____10384 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____10384
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____10420 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____10420
=======
          let binders = _1 :: _2 :: _3 in
          let uu____10382 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____10382
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10418 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____10418
>>>>>>> taramana_pointers_with_codes_modifies
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
<<<<<<< HEAD
      | uu____10463 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
=======
      | uu____10461 -> desugar_term env f
and (typars_of_binders
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.binder Prims.list ->
       (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                         FStar_Pervasives_Native.option)
                                 FStar_Pervasives_Native.tuple2 Prims.list)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun bs  ->
      let uu____10466 =
        FStar_List.fold_left
          (fun uu____10502  ->
             fun b  ->
               match uu____10502 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
<<<<<<< HEAD
                       (let uu___241_10556 = b  in
=======
                       (let uu___245_10554 = b in
>>>>>>> taramana_pointers_with_codes_modifies
                        {
                          FStar_Parser_AST.b =
                            (uu___245_10554.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___245_10554.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
<<<<<<< HEAD
                            (uu___241_10556.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____10573 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____10573 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___242_10593 = a1  in
=======
                            (uu___245_10554.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____10571 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____10571 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___246_10591 = a1 in
>>>>>>> taramana_pointers_with_codes_modifies
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___246_10591.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___246_10591.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____10608 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
<<<<<<< HEAD
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____10468 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
=======
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____10466 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and (desugar_binder
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.binder ->
       (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
<<<<<<< HEAD
          let uu____10697 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____10697)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____10702 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____10702)
=======
          let uu____10695 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____10695)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____10700 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____10700)
>>>>>>> taramana_pointers_with_codes_modifies
      | FStar_Parser_AST.TVariable x ->
          let uu____10704 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
<<<<<<< HEAD
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____10706)
      | FStar_Parser_AST.NoName t ->
          let uu____10714 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____10714)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list
  =
=======
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____10704)
      | FStar_Parser_AST.NoName t ->
          let uu____10712 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____10712)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)
let (mk_data_discriminators
  :FStar_Syntax_Syntax.qualifier Prims.list ->
     FStar_ToSyntax_Env.env ->
       FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___216_10748  ->
                  match uu___216_10748 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
<<<<<<< HEAD
                  | uu____10751 -> false))
           in
        let quals2 q =
          let uu____10762 =
            (let uu____10765 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____10765) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____10762
=======
                  | uu____10749 -> false)) in
        let quals2 q =
          let uu____10760 =
            (let uu____10763 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____10763) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____10760
>>>>>>> taramana_pointers_with_codes_modifies
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
<<<<<<< HEAD
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____10778 =
=======
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____10776 =
>>>>>>> taramana_pointers_with_codes_modifies
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
                  FStar_Syntax_Syntax.sigquals = uu____10776;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
<<<<<<< HEAD
  
let mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_ToSyntax_Env.env ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list
  =
=======
let (mk_indexed_projector_names
  :FStar_Syntax_Syntax.qualifier Prims.list ->
     FStar_Syntax_Syntax.fv_qual ->
       FStar_ToSyntax_Env.env ->
         FStar_Ident.lid ->
           FStar_Syntax_Syntax.binder Prims.list ->
             FStar_Syntax_Syntax.sigelt Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
<<<<<<< HEAD
            let p = FStar_Ident.range_of_lid lid  in
            let uu____10814 =
=======
            let p = FStar_Ident.range_of_lid lid in
            let uu____10812 =
>>>>>>> taramana_pointers_with_codes_modifies
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____10842  ->
                        match uu____10842 with
                        | (x,uu____10850) ->
                            let uu____10851 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
<<<<<<< HEAD
                                i
                               in
                            (match uu____10853 with
                             | (field_name,uu____10861) ->
                                 let only_decl =
                                   ((let uu____10865 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
=======
                                i in
                            (match uu____10851 with
                             | (field_name,uu____10859) ->
                                 let only_decl =
                                   ((let uu____10863 =
                                       FStar_ToSyntax_Env.current_module env in
>>>>>>> taramana_pointers_with_codes_modifies
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____10863)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____10865 =
                                        let uu____10866 =
                                          FStar_ToSyntax_Env.current_module
<<<<<<< HEAD
                                            env
                                           in
                                        uu____10868.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____10867)
                                    in
=======
                                            env in
                                        uu____10866.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____10865) in
>>>>>>> taramana_pointers_with_codes_modifies
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____10880 =
                                       FStar_List.filter
                                         (fun uu___217_10884  ->
                                            match uu___217_10884 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
<<<<<<< HEAD
                                            | uu____10887 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____10882
                                   else q  in
=======
                                            | uu____10885 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____10880
                                   else q in
>>>>>>> taramana_pointers_with_codes_modifies
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___218_10898  ->
                                             match uu___218_10898 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
<<<<<<< HEAD
                                             | uu____10901 -> false))
                                      in
=======
                                             | uu____10899 -> false)) in
>>>>>>> taramana_pointers_with_codes_modifies
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
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____10907 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
<<<<<<< HEAD
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____10909
=======
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____10907
>>>>>>> taramana_pointers_with_codes_modifies
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____10912 =
                                        let uu____10917 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
<<<<<<< HEAD
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____10919  in
=======
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____10917 in
>>>>>>> taramana_pointers_with_codes_modifies
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____10912;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____10919 =
                                        let uu____10920 =
                                          let uu____10927 =
                                            let uu____10930 =
                                              let uu____10931 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____10931
                                                (fun fv  ->
<<<<<<< HEAD
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____10932]  in
                                          ((false, [lb]), uu____10929)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____10922
                                         in
=======
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____10930] in
                                          ((false, [lb]), uu____10927) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____10920 in
>>>>>>> taramana_pointers_with_codes_modifies
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____10919;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
<<<<<<< HEAD
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____10814 FStar_List.flatten
  
let mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
=======
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____10812 FStar_List.flatten
let (mk_data_projector_names
  :FStar_Syntax_Syntax.qualifier Prims.list ->
     FStar_ToSyntax_Env.env ->
       FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____10978,t,uu____10980,n1,uu____10982) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
<<<<<<< HEAD
            let uu____10989 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____10989 with
             | (formals,uu____11005) ->
=======
            let uu____10987 = FStar_Syntax_Util.arrow_formals t in
            (match uu____10987 with
             | (formals,uu____11003) ->
>>>>>>> taramana_pointers_with_codes_modifies
                 (match formals with
                  | [] -> []
                  | uu____11026 ->
                      let filter_records uu___219_11038 =
                        match uu___219_11038 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11041,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
<<<<<<< HEAD
                        | uu____11055 -> FStar_Pervasives_Native.None  in
=======
                        | uu____11053 -> FStar_Pervasives_Native.None in
>>>>>>> taramana_pointers_with_codes_modifies
                      let fv_qual =
                        let uu____11055 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
<<<<<<< HEAD
                            filter_records
                           in
                        match uu____11057 with
=======
                            filter_records in
                        match uu____11055 with
>>>>>>> taramana_pointers_with_codes_modifies
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
<<<<<<< HEAD
                        else iquals  in
                      let uu____11067 = FStar_Util.first_N n1 formals  in
                      (match uu____11067 with
                       | (uu____11090,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11116 -> []
  
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
=======
                        else iquals in
                      let uu____11065 = FStar_Util.first_N n1 formals in
                      (match uu____11065 with
                       | (uu____11088,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11114 -> []
let (mk_typ_abbrev
  :FStar_Ident.lident ->
     FStar_Syntax_Syntax.univ_name Prims.list ->
       (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term ->
             FStar_Ident.lident Prims.list ->
               FStar_Syntax_Syntax.qualifier Prims.list ->
                 FStar_Range.range -> FStar_Syntax_Syntax.sigelt)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun k  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____11172 =
                      FStar_All.pipe_right quals
<<<<<<< HEAD
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____11174
                    then
                      let uu____11177 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____11177
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
=======
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11172
                    then
                      let uu____11175 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11175
                    else FStar_Syntax_Util.incr_delta_qualifier t in
>>>>>>> taramana_pointers_with_codes_modifies
                  let lb =
                    let uu____11178 =
                      let uu____11183 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
<<<<<<< HEAD
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____11185  in
                    let uu____11186 =
                      let uu____11189 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____11189  in
                    let uu____11192 = no_annot_abs typars t  in
=======
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11183 in
                    let uu____11184 =
                      let uu____11187 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11187 in
                    let uu____11190 = no_annot_abs typars t in
>>>>>>> taramana_pointers_with_codes_modifies
                    {
                      FStar_Syntax_Syntax.lbname = uu____11178;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11184;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
<<<<<<< HEAD
                      FStar_Syntax_Syntax.lbdef = uu____11192
                    }  in
=======
                      FStar_Syntax_Syntax.lbdef = uu____11190
                    } in
>>>>>>> taramana_pointers_with_codes_modifies
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
                  }
<<<<<<< HEAD
  
let rec desugar_tycon :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
=======
let rec (desugar_tycon
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.decl ->
       FStar_Syntax_Syntax.qualifier Prims.list ->
         FStar_Parser_AST.tycon Prims.list ->
           (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
<<<<<<< HEAD
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___216_11241 =
            match uu___216_11241 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11243,uu____11244) ->
=======
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___220_11239 =
            match uu___220_11239 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11241,uu____11242) ->
>>>>>>> taramana_pointers_with_codes_modifies
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11252,uu____11253,uu____11254) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11264,uu____11265,uu____11266) -> id
            | FStar_Parser_AST.TyconVariant
<<<<<<< HEAD
                (id,uu____11298,uu____11299,uu____11300) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11342) ->
                let uu____11343 =
                  let uu____11344 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____11344  in
                FStar_Parser_AST.mk_term uu____11343 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11346 =
                  let uu____11347 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____11347  in
                FStar_Parser_AST.mk_term uu____11346 x.FStar_Ident.idRange
=======
                (id,uu____11296,uu____11297,uu____11298) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11340) ->
                let uu____11341 =
                  let uu____11342 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11342 in
                FStar_Parser_AST.mk_term uu____11341 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11344 =
                  let uu____11345 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11345 in
                FStar_Parser_AST.mk_term uu____11344 x.FStar_Ident.idRange
>>>>>>> taramana_pointers_with_codes_modifies
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____11347) ->
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
<<<<<<< HEAD
              | uu____11372 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11378 =
                     let uu____11379 =
                       let uu____11386 = binder_to_term b  in
                       (out, uu____11386, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____11379  in
                   FStar_Parser_AST.mk_term uu____11378
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___217_11396 =
            match uu___217_11396 with
=======
              | uu____11370 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11376 =
                     let uu____11377 =
                       let uu____11384 = binder_to_term b in
                       (out, uu____11384, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____11377 in
                   FStar_Parser_AST.mk_term uu____11376
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___221_11394 =
            match uu___221_11394 with
>>>>>>> taramana_pointers_with_codes_modifies
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____11449  ->
                       match uu____11449 with
                       | (x,t,uu____11460) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
<<<<<<< HEAD
                  let uu____11468 =
                    let uu____11469 =
                      let uu____11470 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____11470  in
                    FStar_Parser_AST.mk_term uu____11469
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____11468 parms  in
=======
                  let uu____11466 =
                    let uu____11467 =
                      let uu____11468 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____11468 in
                    FStar_Parser_AST.mk_term uu____11467
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____11466 parms in
>>>>>>> taramana_pointers_with_codes_modifies
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
<<<<<<< HEAD
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____11474 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11501  ->
                          match uu____11501 with
                          | (x,uu____11511,uu____11512) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
=======
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____11472 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11499  ->
                          match uu____11499 with
                          | (x,uu____11509,uu____11510) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
>>>>>>> taramana_pointers_with_codes_modifies
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
<<<<<<< HEAD
                  uu____11474)
            | uu____11565 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___218_11596 =
            match uu___218_11596 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____11620 = typars_of_binders _env binders  in
                (match uu____11620 with
=======
                  uu____11472)
            | uu____11563 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___222_11594 =
            match uu___222_11594 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____11618 = typars_of_binders _env binders in
                (match uu____11618 with
>>>>>>> taramana_pointers_with_codes_modifies
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
<<<<<<< HEAD
                       let uu____11666 =
                         let uu____11667 =
                           let uu____11668 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____11668  in
                         FStar_Parser_AST.mk_term uu____11667
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____11666 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
=======
                       let uu____11664 =
                         let uu____11665 =
                           let uu____11666 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____11666 in
                         FStar_Parser_AST.mk_term uu____11665
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____11664 binders in
                     let qlid = FStar_ToSyntax_Env.qualify _env id in
                     let typars1 = FStar_Syntax_Subst.close_binders typars in
                     let k1 = FStar_Syntax_Subst.close typars1 k in
>>>>>>> taramana_pointers_with_codes_modifies
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
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
<<<<<<< HEAD
            | uu____11681 -> failwith "Unexpected tycon"  in
=======
            | uu____11679 -> failwith "Unexpected tycon" in
>>>>>>> taramana_pointers_with_codes_modifies
          let push_tparams env1 bs =
            let uu____11723 =
              FStar_List.fold_left
                (fun uu____11763  ->
                   fun uu____11764  ->
                     match (uu____11763, uu____11764) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____11855 =
                           FStar_ToSyntax_Env.push_bv env2
<<<<<<< HEAD
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____11857 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____11725 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
=======
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____11855 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____11723 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
>>>>>>> taramana_pointers_with_codes_modifies
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
<<<<<<< HEAD
                    let uu____11970 = tm_type_z id.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____11970
                | uu____11971 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____11979 = desugar_abstract_tc quals env [] tc  in
              (match uu____11979 with
               | (uu____11992,uu____11993,se,uu____11995) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____11998,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
=======
                    let uu____11968 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____11968
                | uu____11969 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____11977 = desugar_abstract_tc quals env [] tc in
              (match uu____11977 with
               | (uu____11990,uu____11991,se,uu____11993) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____11996,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
>>>>>>> taramana_pointers_with_codes_modifies
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
<<<<<<< HEAD
                             ((let uu____12015 =
                                 let uu____12016 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12016  in
                               if uu____12015
=======
                             ((let uu____12013 =
                                 let uu____12014 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____12014 in
                               if uu____12013
>>>>>>> taramana_pointers_with_codes_modifies
                               then
                                 let uu____12015 =
                                   FStar_Range.string_of_range
<<<<<<< HEAD
                                     se.FStar_Syntax_Syntax.sigrng
                                    in
                                 let uu____12018 =
                                   FStar_Syntax_Print.lid_to_string l  in
=======
                                     se.FStar_Syntax_Syntax.sigrng in
                                 let uu____12016 =
                                   FStar_Syntax_Print.lid_to_string l in
>>>>>>> taramana_pointers_with_codes_modifies
                                 FStar_Util.print2
                                   "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                   uu____12015 uu____12016
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
<<<<<<< HEAD
                           | uu____12025 ->
                               let uu____12026 =
                                 let uu____12029 =
                                   let uu____12030 =
                                     let uu____12043 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12043)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12030
                                    in
                                 FStar_Syntax_Syntax.mk uu____12029  in
                               uu____12026 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___243_12047 = se  in
=======
                           | uu____12023 ->
                               let uu____12024 =
                                 let uu____12027 =
                                   let uu____12028 =
                                     let uu____12041 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12041) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12028 in
                                 FStar_Syntax_Syntax.mk uu____12027 in
                               uu____12024 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___247_12045 = se in
>>>>>>> taramana_pointers_with_codes_modifies
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___247_12045.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___247_12045.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___247_12045.FStar_Syntax_Syntax.sigattrs)
                         }
<<<<<<< HEAD
                     | uu____12050 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____12053 = FStar_ToSyntax_Env.qualify env1 id  in
                     FStar_ToSyntax_Env.push_doc env1 uu____12053
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12068 = typars_of_binders env binders  in
              (match uu____12068 with
=======
                     | uu____12048 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12051 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12051
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12066 = typars_of_binders env binders in
              (match uu____12066 with
>>>>>>> taramana_pointers_with_codes_modifies
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12102 =
                           FStar_Util.for_some
                             (fun uu___223_12104  ->
                                match uu___223_12104 with
                                | FStar_Syntax_Syntax.Effect  -> true
<<<<<<< HEAD
                                | uu____12107 -> false) quals
                            in
                         if uu____12104
=======
                                | uu____12105 -> false) quals in
                         if uu____12102
>>>>>>> taramana_pointers_with_codes_modifies
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____12112 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___224_12116  ->
                               match uu___224_12116 with
                               | FStar_Syntax_Syntax.Logic  -> true
<<<<<<< HEAD
                               | uu____12119 -> false))
                        in
                     if uu____12114
=======
                               | uu____12117 -> false)) in
                     if uu____12112
>>>>>>> taramana_pointers_with_codes_modifies
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id  in
                   let se =
                     let uu____12126 =
                       FStar_All.pipe_right quals1
<<<<<<< HEAD
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____12128
                     then
                       let uu____12131 =
                         let uu____12138 =
                           let uu____12139 = unparen t  in
                           uu____12139.FStar_Parser_AST.tm  in
                         match uu____12138 with
=======
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12126
                     then
                       let uu____12129 =
                         let uu____12136 =
                           let uu____12137 = unparen t in
                           uu____12137.FStar_Parser_AST.tm in
                         match uu____12136 with
>>>>>>> taramana_pointers_with_codes_modifies
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12158 =
                               match FStar_List.rev args with
<<<<<<< HEAD
                               | (last_arg,uu____12190)::args_rev ->
                                   let uu____12202 =
                                     let uu____12203 = unparen last_arg  in
                                     uu____12203.FStar_Parser_AST.tm  in
                                   (match uu____12202 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12231 -> ([], args))
                               | uu____12240 -> ([], args)  in
                             (match uu____12160 with
                              | (cattributes,args1) ->
                                  let uu____12279 =
                                    desugar_attributes env cattributes  in
=======
                               | (last_arg,uu____12188)::args_rev ->
                                   let uu____12200 =
                                     let uu____12201 = unparen last_arg in
                                     uu____12201.FStar_Parser_AST.tm in
                                   (match uu____12200 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12229 -> ([], args))
                               | uu____12238 -> ([], args) in
                             (match uu____12158 with
                              | (cattributes,args1) ->
                                  let uu____12277 =
                                    desugar_attributes env cattributes in
>>>>>>> taramana_pointers_with_codes_modifies
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
<<<<<<< HEAD
                                      t.FStar_Parser_AST.level), uu____12279))
                         | uu____12290 -> (t, [])  in
                       match uu____12131 with
=======
                                      t.FStar_Parser_AST.level), uu____12277))
                         | uu____12288 -> (t, []) in
                       match uu____12129 with
>>>>>>> taramana_pointers_with_codes_modifies
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
                                  (fun uu___225_12310  ->
                                     match uu___225_12310 with
                                     | FStar_Syntax_Syntax.Effect  -> false
<<<<<<< HEAD
                                     | uu____12313 -> true))
                              in
=======
                                     | uu____12311 -> true)) in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
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
<<<<<<< HEAD
          | (FStar_Parser_AST.TyconRecord uu____12324)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____12348 = tycon_record_as_variant trec  in
              (match uu____12348 with
               | (t,fs) ->
                   let uu____12365 =
                     let uu____12368 =
                       let uu____12369 =
                         let uu____12378 =
                           let uu____12381 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____12381  in
                         (uu____12378, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____12369  in
                     uu____12368 :: quals  in
                   desugar_tycon env d uu____12365 [t])
          | uu____12386::uu____12387 ->
              let env0 = env  in
=======
          | (FStar_Parser_AST.TyconRecord uu____12322)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____12346 = tycon_record_as_variant trec in
              (match uu____12346 with
               | (t,fs) ->
                   let uu____12363 =
                     let uu____12366 =
                       let uu____12367 =
                         let uu____12376 =
                           let uu____12379 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____12379 in
                         (uu____12376, fs) in
                       FStar_Syntax_Syntax.RecordType uu____12367 in
                     uu____12366 :: quals in
                   desugar_tycon env d uu____12363 [t])
          | uu____12384::uu____12385 ->
              let env0 = env in
>>>>>>> taramana_pointers_with_codes_modifies
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
<<<<<<< HEAD
                let uu____12548 = et  in
                match uu____12548 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____12773 ->
                         let trec = tc  in
                         let uu____12797 = tycon_record_as_variant trec  in
                         (match uu____12797 with
=======
                let uu____12546 = et in
                match uu____12546 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____12771 ->
                         let trec = tc in
                         let uu____12795 = tycon_record_as_variant trec in
                         (match uu____12795 with
>>>>>>> taramana_pointers_with_codes_modifies
                          | (t,fs) ->
                              let uu____12854 =
                                let uu____12857 =
                                  let uu____12858 =
                                    let uu____12867 =
                                      let uu____12870 =
                                        FStar_ToSyntax_Env.current_module
<<<<<<< HEAD
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____12872  in
                                    (uu____12869, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____12860
                                   in
                                uu____12859 :: quals1  in
                              collect_tcs uu____12856 (env1, tcs1) t)
=======
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____12870 in
                                    (uu____12867, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____12858 in
                                uu____12857 :: quals1 in
                              collect_tcs uu____12854 (env1, tcs1) t)
>>>>>>> taramana_pointers_with_codes_modifies
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____12957 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
<<<<<<< HEAD
                                (id, binders, kopt))
                            in
                         (match uu____12959 with
                          | (env2,uu____13019,se,tconstr) ->
=======
                                (id, binders, kopt)) in
                         (match uu____12957 with
                          | (env2,uu____13017,se,tconstr) ->
>>>>>>> taramana_pointers_with_codes_modifies
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13166 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
<<<<<<< HEAD
                                (id, binders, kopt))
                            in
                         (match uu____13168 with
                          | (env2,uu____13228,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13353 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____13400 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____13400 with
=======
                                (id, binders, kopt)) in
                         (match uu____13166 with
                          | (env2,uu____13226,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13351 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____13398 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____13398 with
>>>>>>> taramana_pointers_with_codes_modifies
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___227_13909  ->
                             match uu___227_13909 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____13976,uu____13977);
                                    FStar_Syntax_Syntax.sigrng = uu____13978;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____13979;
                                    FStar_Syntax_Syntax.sigmeta = uu____13980;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____13981;_},binders,t,quals1)
                                 ->
                                 let t1 =
<<<<<<< HEAD
                                   let uu____14044 =
                                     typars_of_binders env1 binders  in
                                   match uu____14044 with
                                   | (env2,tpars1) ->
                                       let uu____14075 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14075 with
=======
                                   let uu____14042 =
                                     typars_of_binders env1 binders in
                                   match uu____14042 with
                                   | (env2,tpars1) ->
                                       let uu____14073 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14073 with
>>>>>>> taramana_pointers_with_codes_modifies
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
<<<<<<< HEAD
                                              t1)
                                    in
                                 let uu____14108 =
                                   let uu____14129 =
=======
                                              t1) in
                                 let uu____14106 =
                                   let uu____14127 =
>>>>>>> taramana_pointers_with_codes_modifies
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
<<<<<<< HEAD
                                     uu____14129)
                                    in
                                 [uu____14108]
=======
                                     uu____14127) in
                                 [uu____14106]
>>>>>>> taramana_pointers_with_codes_modifies
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14195);
                                    FStar_Syntax_Syntax.sigrng = uu____14196;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14198;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14199;_},constrs,tconstr,quals1)
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
<<<<<<< HEAD
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____14297 = push_tparams env1 tpars
                                    in
                                 (match uu____14297 with
=======
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____14295 = push_tparams env1 tpars in
                                 (match uu____14295 with
>>>>>>> taramana_pointers_with_codes_modifies
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____14372  ->
                                             match uu____14372 with
                                             | (x,uu____14386) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
<<<<<<< HEAD
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____14396 =
                                        let uu____14425 =
=======
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____14394 =
                                        let uu____14423 =
>>>>>>> taramana_pointers_with_codes_modifies
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____14537  ->
                                                  match uu____14537 with
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
<<<<<<< HEAD
                                                        let uu____14595 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____14595
                                                         in
=======
                                                        let uu____14593 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____14593 in
>>>>>>> taramana_pointers_with_codes_modifies
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___226_14604
                                                                 ->
                                                                match uu___226_14604
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
<<<<<<< HEAD
                                                                | uu____14618
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____14626 =
                                                        let uu____14647 =
                                                          let uu____14648 =
                                                            let uu____14649 =
                                                              let uu____14664
=======
                                                                | uu____14616
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____14624 =
                                                        let uu____14645 =
                                                          let uu____14646 =
                                                            let uu____14647 =
                                                              let uu____14662
>>>>>>> taramana_pointers_with_codes_modifies
                                                                =
                                                                let uu____14665
                                                                  =
                                                                  let uu____14668
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
<<<<<<< HEAD
                                                                    uu____14670
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____14667
                                                                 in
=======
                                                                    uu____14668 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____14665 in
>>>>>>> taramana_pointers_with_codes_modifies
                                                              (name, univs1,
                                                                uu____14662,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
                                                              uu____14649
                                                             in
=======
                                                              uu____14647 in
>>>>>>> taramana_pointers_with_codes_modifies
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____14646;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
<<<<<<< HEAD
                                                          uu____14647)
                                                         in
                                                      (name, uu____14626)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14425
                                         in
                                      (match uu____14396 with
=======
                                                          uu____14645) in
                                                      (name, uu____14624))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14423 in
                                      (match uu____14394 with
>>>>>>> taramana_pointers_with_codes_modifies
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
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 []
                                             })
                                           :: constrs1))
<<<<<<< HEAD
                             | uu____14909 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15041  ->
                             match uu____15041 with
                             | (name_doc,uu____15069,uu____15070) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15150  ->
                             match uu____15150 with
                             | (uu____15171,uu____15172,se) -> se))
                      in
                   let uu____15202 =
                     let uu____15209 =
=======
                             | uu____14907 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15039  ->
                             match uu____15039 with
                             | (name_doc,uu____15067,uu____15068) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15148  ->
                             match uu____15148 with
                             | (uu____15169,uu____15170,se) -> se)) in
                   let uu____15200 =
                     let uu____15207 =
>>>>>>> taramana_pointers_with_codes_modifies
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
<<<<<<< HEAD
                       sigelts quals uu____15209 rng
                      in
                   (match uu____15202 with
=======
                       sigelts quals uu____15207 rng in
                   (match uu____15200 with
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                               (fun uu____15275  ->
                                  match uu____15275 with
                                  | (uu____15298,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
=======
                               (fun uu____15273  ->
                                  match uu____15273 with
                                  | (uu____15296,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
>>>>>>> taramana_pointers_with_codes_modifies
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____15347,tps,k,uu____15350,constrs)
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
<<<<<<< HEAD
                                  | uu____15371 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
=======
                                  | uu____15369 -> [])) in
                        let ops = FStar_List.append discs data_ops in
>>>>>>> taramana_pointers_with_codes_modifies
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____15386  ->
                                 match uu____15386 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
<<<<<<< HEAD
  
let desugar_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2
  =
=======
let (desugar_binders
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.binder Prims.list ->
       (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun binders  ->
      let uu____15423 =
        FStar_List.fold_left
          (fun uu____15446  ->
             fun b  ->
               match uu____15446 with
               | (env1,binders1) ->
<<<<<<< HEAD
                   let uu____15468 = desugar_binder env1 b  in
                   (match uu____15468 with
=======
                   let uu____15466 = desugar_binder env1 b in
                   (match uu____15466 with
>>>>>>> taramana_pointers_with_codes_modifies
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15483 =
                          as_binder env1 b.FStar_Parser_AST.aqual
<<<<<<< HEAD
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____15485 with
=======
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____15483 with
>>>>>>> taramana_pointers_with_codes_modifies
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____15500 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
<<<<<<< HEAD
          binders
         in
      match uu____15425 with
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
=======
          binders in
      match uu____15423 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
let rec (desugar_effect
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.decl ->
       FStar_Parser_AST.qualifiers ->
         FStar_Ident.ident ->
           FStar_Parser_AST.binder Prims.list ->
             FStar_Parser_AST.term ->
               FStar_Parser_AST.decl Prims.list ->
                 (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt
                                           Prims.list)
                   FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
<<<<<<< HEAD
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                let uu____15616 = desugar_binders monad_env eff_binders  in
                match uu____15616 with
=======
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                let uu____15614 = desugar_binders monad_env eff_binders in
                match uu____15614 with
>>>>>>> taramana_pointers_with_codes_modifies
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
<<<<<<< HEAD
                      let uu____15637 =
                        let uu____15638 =
                          let uu____15645 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____15645  in
                        FStar_List.length uu____15638  in
                      uu____15637 = (Prims.parse_int "1")  in
=======
                      let uu____15635 =
                        let uu____15636 =
                          let uu____15643 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____15643 in
                        FStar_List.length uu____15636 in
                      uu____15635 = (Prims.parse_int "1") in
>>>>>>> taramana_pointers_with_codes_modifies
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
                          (uu____15685,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____15687,uu____15688,uu____15689),uu____15690)::[])
                          -> FStar_Ident.text_of_id name
<<<<<<< HEAD
                      | uu____15725 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____15726 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____15738 = name_of_eff_decl decl  in
                           FStar_List.mem uu____15738 mandatory_members)
                        eff_decls
                       in
                    (match uu____15726 with
=======
                      | uu____15723 ->
                          failwith "Malformed effect member declaration." in
                    let uu____15724 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____15736 = name_of_eff_decl decl in
                           FStar_List.mem uu____15736 mandatory_members)
                        eff_decls in
                    (match uu____15724 with
>>>>>>> taramana_pointers_with_codes_modifies
                     | (mandatory_members_decls,actions) ->
                         let uu____15753 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____15782  ->
                                   fun decl  ->
                                     match uu____15782 with
                                     | (env2,out) ->
<<<<<<< HEAD
                                         let uu____15804 =
                                           desugar_decl env2 decl  in
                                         (match uu____15804 with
                                          | (env3,ses) ->
                                              let uu____15817 =
                                                let uu____15820 =
                                                  FStar_List.hd ses  in
                                                uu____15820 :: out  in
                                              (env3, uu____15817)))
                                (env1, []))
                            in
                         (match uu____15755 with
=======
                                         let uu____15802 =
                                           desugar_decl env2 decl in
                                         (match uu____15802 with
                                          | (env3,ses) ->
                                              let uu____15815 =
                                                let uu____15818 =
                                                  FStar_List.hd ses in
                                                uu____15818 :: out in
                                              (env3, uu____15815)))
                                (env1, [])) in
                         (match uu____15753 with
>>>>>>> taramana_pointers_with_codes_modifies
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____15886,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____15889,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____15890,
                                                                (def,uu____15892)::
                                                                (cps_type,uu____15894)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____15895;
                                                             FStar_Parser_AST.level
                                                               = uu____15896;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____15948 =
                                              desugar_binders env2
<<<<<<< HEAD
                                                action_params
                                               in
                                            (match uu____15950 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____15970 =
                                                   let uu____15971 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____15972 =
                                                     let uu____15973 =
                                                       desugar_term env3 def
                                                        in
=======
                                                action_params in
                                            (match uu____15948 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____15968 =
                                                   let uu____15969 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____15970 =
                                                     let uu____15971 =
                                                       desugar_term env3 def in
>>>>>>> taramana_pointers_with_codes_modifies
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
<<<<<<< HEAD
                                                       uu____15973
                                                      in
                                                   let uu____15978 =
                                                     let uu____15979 =
=======
                                                       uu____15971 in
                                                   let uu____15976 =
                                                     let uu____15977 =
>>>>>>> taramana_pointers_with_codes_modifies
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
<<<<<<< HEAD
                                                       uu____15979
                                                      in
=======
                                                       uu____15977 in
>>>>>>> taramana_pointers_with_codes_modifies
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____15969;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____15970;
                                                     FStar_Syntax_Syntax.action_typ
<<<<<<< HEAD
                                                       = uu____15978
                                                   }  in
                                                 (uu____15970, doc1))
=======
                                                       = uu____15976
                                                   } in
                                                 (uu____15968, doc1))
>>>>>>> taramana_pointers_with_codes_modifies
                                        | FStar_Parser_AST.Tycon
                                            (uu____15984,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____15987,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16022 =
                                              desugar_binders env2
<<<<<<< HEAD
                                                action_params
                                               in
                                            (match uu____16024 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16044 =
                                                   let uu____16045 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16046 =
                                                     let uu____16047 =
                                                       desugar_term env3 defn
                                                        in
=======
                                                action_params in
                                            (match uu____16022 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16042 =
                                                   let uu____16043 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16044 =
                                                     let uu____16045 =
                                                       desugar_term env3 defn in
>>>>>>> taramana_pointers_with_codes_modifies
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
<<<<<<< HEAD
                                                       uu____16047
                                                      in
=======
                                                       uu____16045 in
>>>>>>> taramana_pointers_with_codes_modifies
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16043;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16044;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
<<<<<<< HEAD
                                                   }  in
                                                 (uu____16044, doc1))
                                        | uu____16054 ->
=======
                                                   } in
                                                 (uu____16042, doc1))
                                        | uu____16052 ->
>>>>>>> taramana_pointers_with_codes_modifies
                                            FStar_Exn.raise
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
<<<<<<< HEAD
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____16084 =
                                  let uu____16085 =
=======
                                       (s, (d.FStar_Parser_AST.drange))) in
                                let uu____16082 =
                                  let uu____16083 =
>>>>>>> taramana_pointers_with_codes_modifies
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
<<<<<<< HEAD
                                    uu____16085
                                   in
                                ([], uu____16084)  in
=======
                                    uu____16083 in
                                ([], uu____16082) in
>>>>>>> taramana_pointers_with_codes_modifies
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
                                    let uu____16100 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
<<<<<<< HEAD
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____16102)  in
                                  let uu____16109 =
                                    let uu____16110 =
                                      let uu____16111 =
                                        let uu____16112 = lookup "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____16112
                                         in
                                      let uu____16121 = lookup "return"  in
                                      let uu____16122 = lookup "bind"  in
=======
                                        FStar_Range.dummyRange in
                                    ([], uu____16100) in
                                  let uu____16107 =
                                    let uu____16108 =
                                      let uu____16109 =
                                        let uu____16110 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16110 in
                                      let uu____16119 = lookup "return" in
                                      let uu____16120 = lookup "bind" in
>>>>>>> taramana_pointers_with_codes_modifies
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
                                          uu____16109;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16119;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16120;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
<<<<<<< HEAD
                                      uu____16110
                                     in
=======
                                      uu____16108 in
>>>>>>> taramana_pointers_with_codes_modifies
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16107;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___228_16124  ->
                                          match uu___228_16124 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
<<<<<<< HEAD
                                              uu____16127 -> true
                                          | uu____16128 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____16138 =
                                     let uu____16139 =
                                       let uu____16140 = lookup "return_wp"
                                          in
                                       let uu____16141 = lookup "bind_wp"  in
                                       let uu____16142 =
                                         lookup "if_then_else"  in
                                       let uu____16143 = lookup "ite_wp"  in
                                       let uu____16144 = lookup "stronger"
                                          in
                                       let uu____16145 = lookup "close_wp"
                                          in
                                       let uu____16146 = lookup "assert_p"
                                          in
                                       let uu____16147 = lookup "assume_p"
                                          in
                                       let uu____16148 = lookup "null_wp"  in
                                       let uu____16149 = lookup "trivial"  in
                                       let uu____16150 =
                                         if rr
                                         then
                                           let uu____16151 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16151
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____16167 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____16169 =
                                         if rr then lookup "bind" else un_ts
                                          in
=======
                                              uu____16125 -> true
                                          | uu____16126 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16136 =
                                     let uu____16137 =
                                       let uu____16138 = lookup "return_wp" in
                                       let uu____16139 = lookup "bind_wp" in
                                       let uu____16140 =
                                         lookup "if_then_else" in
                                       let uu____16141 = lookup "ite_wp" in
                                       let uu____16142 = lookup "stronger" in
                                       let uu____16143 = lookup "close_wp" in
                                       let uu____16144 = lookup "assert_p" in
                                       let uu____16145 = lookup "assume_p" in
                                       let uu____16146 = lookup "null_wp" in
                                       let uu____16147 = lookup "trivial" in
                                       let uu____16148 =
                                         if rr
                                         then
                                           let uu____16149 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16149
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16165 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16167 =
                                         if rr then lookup "bind" else un_ts in
>>>>>>> taramana_pointers_with_codes_modifies
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____16138;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16139;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16140;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16141;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16142;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16143;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16144;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16145;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16146;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16147;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16148;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16165;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16167;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
<<<<<<< HEAD
                                       uu____16139
                                      in
=======
                                       uu____16137 in
>>>>>>> taramana_pointers_with_codes_modifies
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16136;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
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
                                        fun uu____16192  ->
                                          match uu____16192 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16206 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
<<<<<<< HEAD
                                                  env5 uu____16208
                                                 in
=======
                                                  env5 uu____16206 in
>>>>>>> taramana_pointers_with_codes_modifies
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                let uu____16208 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
<<<<<<< HEAD
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____16210
=======
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16208
>>>>>>> taramana_pointers_with_codes_modifies
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
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = []
                                    }  in
                                  FStar_ToSyntax_Env.push_sigelt env5
                                    refl_decl
                                else env5  in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))
<<<<<<< HEAD

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
=======
and (desugar_redefine_effect
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.decl ->
       (FStar_Ident.lident FStar_Pervasives_Native.option ->
          FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
         ->
         FStar_Parser_AST.qualifier Prims.list ->
           FStar_Ident.ident ->
             FStar_Parser_AST.binder Prims.list ->
               FStar_Parser_AST.term ->
                 (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt
                                           Prims.list)
                   FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
<<<<<<< HEAD
                let env0 = env  in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name
                   in
                let uu____16241 = desugar_binders env1 eff_binders  in
                match uu____16241 with
                | (env2,binders) ->
                    let uu____16260 =
                      let uu____16279 = head_and_args defn  in
                      match uu____16279 with
=======
                let env0 = env in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                let uu____16239 = desugar_binders env1 eff_binders in
                match uu____16239 with
                | (env2,binders) ->
                    let uu____16258 =
                      let uu____16277 = head_and_args defn in
                      match uu____16277 with
>>>>>>> taramana_pointers_with_codes_modifies
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____16322 ->
                                let uu____16323 =
                                  let uu____16324 =
                                    let uu____16329 =
                                      let uu____16330 =
                                        let uu____16331 =
                                          FStar_Parser_AST.term_to_string
<<<<<<< HEAD
                                            head1
                                           in
                                        Prims.strcat uu____16333 " not found"
                                         in
                                      Prims.strcat "Effect " uu____16332  in
                                    (uu____16331,
                                      (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____16326  in
                                FStar_Exn.raise uu____16325
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____16335 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16365)::args_rev ->
                                let uu____16377 =
                                  let uu____16378 = unparen last_arg  in
                                  uu____16378.FStar_Parser_AST.tm  in
                                (match uu____16377 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16406 -> ([], args))
                            | uu____16415 -> ([], args)  in
                          (match uu____16335 with
                           | (cattributes,args1) ->
                               let uu____16466 = desugar_args env2 args1  in
                               let uu____16475 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____16466, uu____16475))
                       in
                    (match uu____16260 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____16534 =
                           match uu____16534 with
                           | (uu____16547,x) ->
                               let uu____16553 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____16553 with
=======
                                            head1 in
                                        Prims.strcat uu____16331 " not found" in
                                      Prims.strcat "Effect " uu____16330 in
                                    (uu____16329,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____16324 in
                                FStar_Exn.raise uu____16323 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____16333 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16363)::args_rev ->
                                let uu____16375 =
                                  let uu____16376 = unparen last_arg in
                                  uu____16376.FStar_Parser_AST.tm in
                                (match uu____16375 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16404 -> ([], args))
                            | uu____16413 -> ([], args) in
                          (match uu____16333 with
                           | (cattributes,args1) ->
                               let uu____16464 = desugar_args env2 args1 in
                               let uu____16473 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____16464, uu____16473)) in
                    (match uu____16258 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____16532 =
                           match uu____16532 with
                           | (uu____16545,x) ->
                               let uu____16551 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____16551 with
>>>>>>> taramana_pointers_with_codes_modifies
                                | (edb,x1) ->
                                    (if
                                       (FStar_List.length args) <>
                                         (FStar_List.length edb)
                                     then
                                       FStar_Exn.raise
                                         (FStar_Errors.Error
                                            ("Unexpected number of arguments to effect constructor",
                                              (defn.FStar_Parser_AST.range)))
                                     else ();
                                     (let s =
                                        FStar_Syntax_Util.subst_of_list edb
<<<<<<< HEAD
                                          args
                                         in
                                      let uu____16579 =
                                        let uu____16580 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____16580
                                         in
                                      ([], uu____16579))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____16585 =
                             let uu____16586 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             FStar_Pervasives_Native.snd uu____16586  in
                           let uu____16597 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____16598 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____16599 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____16600 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____16601 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____16602 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____16603 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____16604 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____16605 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____16606 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____16607 =
                             let uu____16608 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             FStar_Pervasives_Native.snd uu____16608  in
                           let uu____16619 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____16620 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____16621 =
=======
                                          args in
                                      let uu____16577 =
                                        let uu____16578 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____16578 in
                                      ([], uu____16577)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____16583 =
                             let uu____16584 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____16584 in
                           let uu____16595 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____16596 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____16597 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____16598 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____16599 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____16600 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____16601 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____16602 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____16603 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____16604 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____16605 =
                             let uu____16606 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____16606 in
                           let uu____16617 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____16618 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____16619 =
>>>>>>> taramana_pointers_with_codes_modifies
                             FStar_List.map
                               (fun action  ->
                                  let uu____16627 =
                                    FStar_ToSyntax_Env.qualify env2
<<<<<<< HEAD
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____16630 =
                                    let uu____16631 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    FStar_Pervasives_Native.snd uu____16631
                                     in
                                  let uu____16642 =
                                    let uu____16643 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    FStar_Pervasives_Native.snd uu____16643
                                     in
=======
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____16628 =
                                    let uu____16629 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____16629 in
                                  let uu____16640 =
                                    let uu____16641 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____16641 in
>>>>>>> taramana_pointers_with_codes_modifies
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____16627;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____16628;
                                    FStar_Syntax_Syntax.action_typ =
<<<<<<< HEAD
                                      uu____16642
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
=======
                                      uu____16640
                                  }) ed.FStar_Syntax_Syntax.actions in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
<<<<<<< HEAD
                             FStar_Syntax_Syntax.signature = uu____16585;
                             FStar_Syntax_Syntax.ret_wp = uu____16597;
                             FStar_Syntax_Syntax.bind_wp = uu____16598;
                             FStar_Syntax_Syntax.if_then_else = uu____16599;
                             FStar_Syntax_Syntax.ite_wp = uu____16600;
                             FStar_Syntax_Syntax.stronger = uu____16601;
                             FStar_Syntax_Syntax.close_wp = uu____16602;
                             FStar_Syntax_Syntax.assert_p = uu____16603;
                             FStar_Syntax_Syntax.assume_p = uu____16604;
                             FStar_Syntax_Syntax.null_wp = uu____16605;
                             FStar_Syntax_Syntax.trivial = uu____16606;
                             FStar_Syntax_Syntax.repr = uu____16607;
                             FStar_Syntax_Syntax.return_repr = uu____16619;
                             FStar_Syntax_Syntax.bind_repr = uu____16620;
                             FStar_Syntax_Syntax.actions = uu____16621
                           }  in
=======
                             FStar_Syntax_Syntax.signature = uu____16583;
                             FStar_Syntax_Syntax.ret_wp = uu____16595;
                             FStar_Syntax_Syntax.bind_wp = uu____16596;
                             FStar_Syntax_Syntax.if_then_else = uu____16597;
                             FStar_Syntax_Syntax.ite_wp = uu____16598;
                             FStar_Syntax_Syntax.stronger = uu____16599;
                             FStar_Syntax_Syntax.close_wp = uu____16600;
                             FStar_Syntax_Syntax.assert_p = uu____16601;
                             FStar_Syntax_Syntax.assume_p = uu____16602;
                             FStar_Syntax_Syntax.null_wp = uu____16603;
                             FStar_Syntax_Syntax.trivial = uu____16604;
                             FStar_Syntax_Syntax.repr = uu____16605;
                             FStar_Syntax_Syntax.return_repr = uu____16617;
                             FStar_Syntax_Syntax.bind_repr = uu____16618;
                             FStar_Syntax_Syntax.actions = uu____16619
                           } in
>>>>>>> taramana_pointers_with_codes_modifies
                         let se =
                           let for_free =
                             let uu____16654 =
                               let uu____16655 =
                                 let uu____16662 =
                                   FStar_Syntax_Util.arrow_formals
<<<<<<< HEAD
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 FStar_Pervasives_Native.fst uu____16664  in
                               FStar_List.length uu____16657  in
                             uu____16656 = (Prims.parse_int "1")  in
                           let uu____16693 =
                             let uu____16696 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname)
                                in
                             FStar_List.map uu____16696 quals  in
=======
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____16662 in
                               FStar_List.length uu____16655 in
                             uu____16654 = (Prims.parse_int "1") in
                           let uu____16691 =
                             let uu____16694 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____16694 quals in
>>>>>>> taramana_pointers_with_codes_modifies
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____16691;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
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
                                       let uu____16714 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env5
<<<<<<< HEAD
                                         uu____16716
                                        in
=======
                                         uu____16714 in
>>>>>>> taramana_pointers_with_codes_modifies
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4)
                            in
                         let env6 =
                           let uu____16716 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
<<<<<<< HEAD
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____16718
=======
                                  FStar_Parser_AST.Reflectable) in
                           if uu____16716
>>>>>>> taramana_pointers_with_codes_modifies
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
                                   FStar_Syntax_Syntax.default_sigmeta;
                                 FStar_Syntax_Syntax.sigattrs = []
                               }  in
                             FStar_ToSyntax_Env.push_sigelt env5 refl_decl
                           else env5  in
                         let env7 =
                           FStar_ToSyntax_Env.push_doc env6 mname
                             d.FStar_Parser_AST.doc
                            in
                         (env7, [se]))
<<<<<<< HEAD

and desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____16738 = desugar_decl_noattrs env d  in
      match uu____16738 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let uu____16753 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___244_16759 = sigelt  in
=======
and (desugar_decl
  :env_t ->
     FStar_Parser_AST.decl ->
       (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)=
  fun env  ->
    fun d  ->
      let uu____16736 = desugar_decl_noattrs env d in
      match uu____16736 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let uu____16751 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___248_16757 = sigelt in
>>>>>>> taramana_pointers_with_codes_modifies
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___248_16757.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___248_16757.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___248_16757.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___248_16757.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1
<<<<<<< HEAD
                 }) sigelts
             in
          (env1, uu____16753)

and desugar_decl_noattrs :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
=======
                 }) sigelts in
          (env1, uu____16751)
and (desugar_decl_noattrs
  :env_t ->
     FStar_Parser_AST.decl ->
       (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
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
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____16783 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
<<<<<<< HEAD
          let uu____16801 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____16801, [])
=======
          let uu____16799 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____16799, [])
>>>>>>> taramana_pointers_with_codes_modifies
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
<<<<<<< HEAD
              (fun uu____16840  ->
                 match uu____16840 with | (x,uu____16848) -> x) tcs
             in
          let uu____16853 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____16853 tcs1
=======
              (fun uu____16838  ->
                 match uu____16838 with | (x,uu____16846) -> x) tcs in
          let uu____16851 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____16851 tcs1
>>>>>>> taramana_pointers_with_codes_modifies
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____16873;
                    FStar_Parser_AST.prange = uu____16874;_},uu____16875)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____16884;
                    FStar_Parser_AST.prange = uu____16885;_},uu____16886)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____16901;
                         FStar_Parser_AST.prange = uu____16902;_},uu____16903);
                    FStar_Parser_AST.prange = uu____16904;_},uu____16905)::[]
                   -> false
<<<<<<< HEAD
               | (p,uu____16923)::[] ->
                   let uu____16932 = is_app_pattern p  in
                   Prims.op_Negation uu____16932
               | uu____16933 -> false)
             in
=======
               | (p,uu____16921)::[] ->
                   let uu____16930 = is_app_pattern p in
                   Prims.op_Negation uu____16930
               | uu____16931 -> false) in
>>>>>>> taramana_pointers_with_codes_modifies
          if Prims.op_Negation expand_toplevel_pattern
          then
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
<<<<<<< HEAD
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____16952 =
              let uu____16953 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____16953.FStar_Syntax_Syntax.n  in
            (match uu____16952 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____16961) ->
=======
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
            let ds_lets = desugar_term_maybe_top true env as_inner_let in
            let uu____16950 =
              let uu____16951 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____16951.FStar_Syntax_Syntax.n in
            (match uu____16950 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____16959) ->
>>>>>>> taramana_pointers_with_codes_modifies
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____16992::uu____16993 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____16996 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___229_17009  ->
                               match uu___229_17009 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17012;
                                   FStar_Syntax_Syntax.lbunivs = uu____17013;
                                   FStar_Syntax_Syntax.lbtyp = uu____17014;
                                   FStar_Syntax_Syntax.lbeff = uu____17015;
                                   FStar_Syntax_Syntax.lbdef = uu____17016;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17024;
                                   FStar_Syntax_Syntax.lbtyp = uu____17025;
                                   FStar_Syntax_Syntax.lbeff = uu____17026;
                                   FStar_Syntax_Syntax.lbdef = uu____17027;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____17037 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17051  ->
                             match uu____17051 with
                             | (uu____17056,t) ->
                                 t.FStar_Parser_AST.level =
<<<<<<< HEAD
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____17039
=======
                                   FStar_Parser_AST.Formula)) in
                   if uu____17037
>>>>>>> taramana_pointers_with_codes_modifies
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____17068 =
                     FStar_All.pipe_right quals2
<<<<<<< HEAD
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____17070
=======
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17068
>>>>>>> taramana_pointers_with_codes_modifies
                   then
                     let uu____17077 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
<<<<<<< HEAD
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___245_17093 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___246_17095 = fv  in
=======
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___249_17091 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___250_17093 = fv in
>>>>>>> taramana_pointers_with_codes_modifies
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___250_17093.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___250_17093.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___249_17091.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___249_17091.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___249_17091.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
<<<<<<< HEAD
                                   (uu___245_17093.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____17079)
                   else lbs  in
=======
                                   (uu___249_17091.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17077)
                   else lbs in
>>>>>>> taramana_pointers_with_codes_modifies
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = []
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
             | uu____17125 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17131 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17150 ->
                   failwith
<<<<<<< HEAD
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____17133 with
=======
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17131 with
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                       let uu___247_17176 = pat1  in
=======
                       let uu___251_17174 = pat1 in
>>>>>>> taramana_pointers_with_codes_modifies
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___251_17174.FStar_Parser_AST.prange)
                       }
<<<<<<< HEAD
                   | uu____17177 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___248_17184 = d  in
=======
                   | uu____17175 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___252_17182 = d in
>>>>>>> taramana_pointers_with_codes_modifies
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___252_17182.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___252_17182.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
<<<<<<< HEAD
                          (uu___248_17184.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____17216 id =
                   match uu____17216 with
                   | (env1,ses) ->
                       let main =
                         let uu____17237 =
                           let uu____17238 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____17238  in
                         FStar_Parser_AST.mk_term uu____17237
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id]  in
=======
                          (uu___252_17182.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17214 id =
                   match uu____17214 with
                   | (env1,ses) ->
                       let main =
                         let uu____17235 =
                           let uu____17236 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17236 in
                         FStar_Parser_AST.mk_term uu____17235
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let lid = FStar_Ident.lid_of_ids [id] in
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____17288 = desugar_decl env1 id_decl  in
                       (match uu____17288 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____17306 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____17306 FStar_Util.set_elements
                    in
=======
                                [(bv_pat, body1)])) FStar_Range.dummyRange [] in
                       let uu____17286 = desugar_decl env1 id_decl in
                       (match uu____17286 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17304 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17304 FStar_Util.set_elements in
>>>>>>> taramana_pointers_with_codes_modifies
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
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
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
<<<<<<< HEAD
            let uu____17337 = close_fun env t  in
            desugar_term env uu____17337  in
=======
            let uu____17335 = close_fun env t in desugar_term env uu____17335 in
>>>>>>> taramana_pointers_with_codes_modifies
          let quals1 =
            let uu____17339 =
              (FStar_ToSyntax_Env.iface env) &&
<<<<<<< HEAD
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____17341
=======
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____17339
>>>>>>> taramana_pointers_with_codes_modifies
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let se =
            let uu____17345 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____17345;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____17357 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
<<<<<<< HEAD
              FStar_Parser_Const.exn_lid
             in
          (match uu____17359 with
           | (t,uu____17373) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
=======
              FStar_Parser_Const.exn_lid in
          (match uu____17357 with
           | (t,uu____17371) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
>>>>>>> taramana_pointers_with_codes_modifies
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
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
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
<<<<<<< HEAD
            let uu____17407 =
              let uu____17414 = FStar_Syntax_Syntax.null_binder t  in
              [uu____17414]  in
            let uu____17415 =
              let uu____17418 =
                let uu____17419 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____17419  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17418
               in
            FStar_Syntax_Util.arrow uu____17407 uu____17415  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
=======
            let uu____17405 =
              let uu____17412 = FStar_Syntax_Syntax.null_binder t in
              [uu____17412] in
            let uu____17413 =
              let uu____17416 =
                let uu____17417 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____17417 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17416 in
            FStar_Syntax_Util.arrow uu____17405 uu____17413 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
>>>>>>> taramana_pointers_with_codes_modifies
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
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
<<<<<<< HEAD
            let uu____17481 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____17481 with
            | FStar_Pervasives_Native.None  ->
                let uu____17484 =
                  let uu____17485 =
                    let uu____17490 =
                      let uu____17491 =
                        let uu____17492 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____17492 " not found"  in
                      Prims.strcat "Effect name " uu____17491  in
                    (uu____17490, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____17485  in
                FStar_Exn.raise uu____17484
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____17496 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____17538 =
                  let uu____17547 =
                    let uu____17554 = desugar_term env t  in
                    ([], uu____17554)  in
                  FStar_Pervasives_Native.Some uu____17547  in
                (uu____17538, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____17587 =
                  let uu____17596 =
                    let uu____17603 = desugar_term env wp  in
                    ([], uu____17603)  in
                  FStar_Pervasives_Native.Some uu____17596  in
                let uu____17612 =
                  let uu____17621 =
                    let uu____17628 = desugar_term env t  in
                    ([], uu____17628)  in
                  FStar_Pervasives_Native.Some uu____17621  in
                (uu____17587, uu____17612)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____17654 =
                  let uu____17663 =
                    let uu____17670 = desugar_term env t  in
                    ([], uu____17670)  in
                  FStar_Pervasives_Native.Some uu____17663  in
                (FStar_Pervasives_Native.None, uu____17654)
             in
          (match uu____17496 with
=======
            let uu____17479 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____17479 with
            | FStar_Pervasives_Native.None  ->
                let uu____17482 =
                  let uu____17483 =
                    let uu____17488 =
                      let uu____17489 =
                        let uu____17490 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____17490 " not found" in
                      Prims.strcat "Effect name " uu____17489 in
                    (uu____17488, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____17483 in
                FStar_Exn.raise uu____17482
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____17494 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____17536 =
                  let uu____17545 =
                    let uu____17552 = desugar_term env t in ([], uu____17552) in
                  FStar_Pervasives_Native.Some uu____17545 in
                (uu____17536, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____17585 =
                  let uu____17594 =
                    let uu____17601 = desugar_term env wp in
                    ([], uu____17601) in
                  FStar_Pervasives_Native.Some uu____17594 in
                let uu____17610 =
                  let uu____17619 =
                    let uu____17626 = desugar_term env t in ([], uu____17626) in
                  FStar_Pervasives_Native.Some uu____17619 in
                (uu____17585, uu____17610)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____17652 =
                  let uu____17661 =
                    let uu____17668 = desugar_term env t in ([], uu____17668) in
                  FStar_Pervasives_Native.Some uu____17661 in
                (FStar_Pervasives_Native.None, uu____17652) in
          (match uu____17494 with
>>>>>>> taramana_pointers_with_codes_modifies
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
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               (env, [se]))
<<<<<<< HEAD

let desugar_decls :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelts)
        FStar_Pervasives_Native.tuple2
  =
=======
let (desugar_decls
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.decl Prims.list ->
       (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelts)
         FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____17769  ->
           fun d  ->
             match uu____17769 with
             | (env1,sigelts) ->
<<<<<<< HEAD
                 let uu____17791 = desugar_decl env1 d  in
                 (match uu____17791 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
  
let open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
=======
                 let uu____17789 = desugar_decl env1 d in
                 (match uu____17789 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
let (open_prims_all
  :(FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
     Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
<<<<<<< HEAD
  
let desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3
  =
=======
let (desugar_modul_common
  :FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
     FStar_ToSyntax_Env.env ->
       FStar_Parser_AST.modul ->
         (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
           FStar_Pervasives_Native.tuple3)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____17855) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____17859;
               FStar_Syntax_Syntax.exports = uu____17860;
               FStar_Syntax_Syntax.is_interface = uu____17861;_},FStar_Parser_AST.Module
             (current_lid,uu____17863)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
<<<<<<< HEAD
          | (FStar_Pervasives_Native.Some prev_mod,uu____17873) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____17876 =
=======
          | (FStar_Pervasives_Native.Some prev_mod,uu____17871) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____17874 =
>>>>>>> taramana_pointers_with_codes_modifies
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____17910 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
<<<<<<< HEAD
                  env1 mname
                 in
              (uu____17912, mname, decls, true)
=======
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____17910, mname, decls, true)
>>>>>>> taramana_pointers_with_codes_modifies
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____17927 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
<<<<<<< HEAD
                  env1 mname
                 in
              (uu____17929, mname, decls, false)
           in
        match uu____17876 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____17959 = desugar_decls env2 decls  in
            (match uu____17959 with
=======
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____17927, mname, decls, false) in
        match uu____17874 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____17957 = desugar_decls env2 decls in
            (match uu____17957 with
>>>>>>> taramana_pointers_with_codes_modifies
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
<<<<<<< HEAD
  
let as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul =
=======
let (as_interface :FStar_Parser_AST.modul -> FStar_Parser_AST.modul)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
<<<<<<< HEAD
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul)
          FStar_Pervasives_Native.tuple2
  =
=======
let (desugar_partial_modul
  :FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
     FStar_ToSyntax_Env.env ->
       FStar_Parser_AST.modul ->
         (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul)
           FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____18009 =
            (FStar_Options.interactive ()) &&
<<<<<<< HEAD
              (let uu____18013 =
                 let uu____18014 =
                   let uu____18015 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____18015  in
                 FStar_Util.get_file_extension uu____18014  in
               FStar_List.mem uu____18013 ["fsti"; "fsi"])
             in
          if uu____18011 then as_interface m else m  in
        let uu____18019 = desugar_modul_common curmod env m1  in
        match uu____18019 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18034 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18052 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____18052 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____18068 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____18068
            then
              let uu____18069 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____18069
=======
              (let uu____18011 =
                 let uu____18012 =
                   let uu____18013 = FStar_Options.file_list () in
                   FStar_List.hd uu____18013 in
                 FStar_Util.get_file_extension uu____18012 in
               FStar_List.mem uu____18011 ["fsti"; "fsi"]) in
          if uu____18009 then as_interface m else m in
        let uu____18017 = desugar_modul_common curmod env m1 in
        match uu____18017 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18032 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let (desugar_modul
  :FStar_ToSyntax_Env.env ->
     FStar_Parser_AST.modul ->
       (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul)
         FStar_Pervasives_Native.tuple2)=
  fun env  ->
    fun m  ->
      let uu____18050 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18050 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18066 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18066
            then
              let uu____18067 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18067
>>>>>>> taramana_pointers_with_codes_modifies
            else ());
           (let uu____18069 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
<<<<<<< HEAD
              else env2  in
            (uu____18071, modul)))
  
let desugar_file :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____18087 =
        FStar_List.fold_left
          (fun uu____18107  ->
             fun m  ->
               match uu____18107 with
               | (env1,mods) ->
                   let uu____18127 = desugar_modul env1 m  in
                   (match uu____18127 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____18087 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____18166 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____18166 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____18174 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name
               in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18174
              m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  
=======
              else env2 in
            (uu____18069, modul)))
let (add_modul_to_env
  :FStar_Syntax_Syntax.modul ->
     FStar_ToSyntax_Env.module_inclusion_info ->
       FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env)=
  fun m  ->
    fun mii  ->
      fun en  ->
        let uu____18083 =
          FStar_ToSyntax_Env.prepare_module_or_interface false false en
            m.FStar_Syntax_Syntax.name mii in
        match uu____18083 with
        | (en1,pop_when_done) ->
            let en2 =
              let uu____18091 =
                FStar_ToSyntax_Env.set_current_module en1
                  m.FStar_Syntax_Syntax.name in
              FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18091
                m.FStar_Syntax_Syntax.exports in
            let env = FStar_ToSyntax_Env.finish en2 m in
            if pop_when_done
            then
              FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
                env
            else env
>>>>>>> taramana_pointers_with_codes_modifies
