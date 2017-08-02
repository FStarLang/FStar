open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid: Prims.string -> FStar_Ident.lident =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Tactics"] [s])
      FStar_Range.dummyRange
let by_tactic_lid: FStar_Ident.lident = fstar_tactics_lid "by_tactic"
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____7 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None in
    FStar_All.pipe_right uu____7 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____11 = fstar_tactics_lid s in lid_as_tm uu____11
let fstar_tactics_term: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "term"
let fstar_tactics_env: FStar_Syntax_Syntax.term = mk_tactic_lid_as_term "env"
let fstar_tactics_fvar: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "fvar"
let fstar_tactics_binder: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "binder"
let fstar_tactics_binders: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "binders"
let fstar_tactics_goal: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goal"
let fstar_tactics_goals: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goals"
let fstar_tactics_formula: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "formula"
let fstar_tactics_embed: FStar_Syntax_Syntax.term =
  lid_as_tm FStar_Parser_Const.fstar_tactics_embed_lid
let fstar_tactics_term_view: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "term_view"
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____15
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____19 = fstar_tactics_lid s in lid_as_data_tm uu____19
let fstar_tactics_Failed: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Success"
let fstar_tactics_True_: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "True_"
let fstar_tactics_False_: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "False_"
let fstar_tactics_Eq: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Eq"
let fstar_tactics_And: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "And"
let fstar_tactics_Or: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Or"
let fstar_tactics_Not: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Not"
let fstar_tactics_Implies: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Implies"
let fstar_tactics_Iff: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Iff"
let fstar_tactics_Forall: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Forall"
let fstar_tactics_Exists: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Exists"
let fstar_tactics_App: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "App"
let fstar_tactics_Name: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Name"
let tac_Tv_Var_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_Var"
let tac_Tv_FVar_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_FVar"
let tac_Tv_App_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_App"
let tac_Tv_Abs_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_Abs"
let tac_Tv_Arrow_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_Arrow"
let tac_Tv_Type_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_Type"
let tac_Tv_Refine_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_Refine"
let tac_Tv_Const_lid: FStar_Ident.lident = fstar_tactics_lid "Tv_Const"
let tac_Tv_Var: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_Var_lid
let tac_Tv_FVar: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_FVar_lid
let tac_Tv_App: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_App_lid
let tac_Tv_Abs: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_Abs_lid
let tac_Tv_Arrow: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_Arrow_lid
let tac_Tv_Type: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_Type_lid
let tac_Tv_Refine: FStar_Syntax_Syntax.term =
  lid_as_data_tm tac_Tv_Refine_lid
let tac_Tv_Const: FStar_Syntax_Syntax.term = lid_as_data_tm tac_Tv_Const_lid
let tac_C_Unit_lid: FStar_Ident.lident = fstar_tactics_lid "C_Unit"
let tac_C_Int_lid: FStar_Ident.lident = fstar_tactics_lid "C_Int"
let tac_C_Unit: FStar_Syntax_Syntax.term = lid_as_data_tm tac_C_Unit_lid
let tac_C_Int: FStar_Syntax_Syntax.term = lid_as_data_tm tac_C_Int_lid
let ord_Lt_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Lt"] FStar_Range.dummyRange
let ord_Eq_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Eq"] FStar_Range.dummyRange
let ord_Gt_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Gt"] FStar_Range.dummyRange
let ord_Lt: FStar_Syntax_Syntax.term = lid_as_data_tm ord_Lt_lid
let ord_Eq: FStar_Syntax_Syntax.term = lid_as_data_tm ord_Eq_lid
let ord_Gt: FStar_Syntax_Syntax.term = lid_as_data_tm ord_Gt_lid
let lid_Mktuple2: FStar_Ident.lident =
  FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____28 =
        let uu____29 =
          let uu____30 = FStar_Syntax_Syntax.iarg t in
          let uu____31 =
            let uu____33 = FStar_Syntax_Syntax.as_arg x in [uu____33] in
          uu____30 :: uu____31 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_embed uu____29 in
      uu____28 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let type_of_embedded: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ =
  fun t  ->
    let uu____41 = FStar_Syntax_Util.head_and_args t in
    match uu____41 with
    | (head1,args) ->
        let uu____67 =
          let uu____75 =
            let uu____76 = FStar_Syntax_Util.un_uinst head1 in
            uu____76.FStar_Syntax_Syntax.n in
          (uu____75, args) in
        (match uu____67 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t1,uu____86)::uu____87::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_tactics_embed_lid
             -> t1
         | uu____113 ->
             let uu____121 =
               let uu____122 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term (1): %s"
                 uu____122 in
             failwith uu____121)
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____126 = FStar_Syntax_Util.head_and_args t in
    match uu____126 with
    | (head1,args) ->
        let uu____152 =
          let uu____160 =
            let uu____161 = FStar_Syntax_Util.un_uinst head1 in
            uu____161.FStar_Syntax_Syntax.n in
          (uu____160, args) in
        (match uu____152 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____170::(x,uu____172)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_tactics_embed_lid
             -> x
         | uu____198 ->
             let uu____206 =
               let uu____207 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term (2): %s"
                 uu____207 in
             failwith uu____206)
exception Unembed_failed of Prims.string
let uu___is_Unembed_failed: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unembed_failed uu____214 -> true
    | uu____215 -> false
let __proj__Unembed_failed__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Unembed_failed uu____222 -> uu____222
let embed_binder:
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    let uu____226 =
      FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b) in
    protect_embedded_term fstar_tactics_binder uu____226
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____233 -> failwith "Not an embedded binder"
let embed_pair x embed_a t_a embed_b t_b =
  let uu____277 =
    let uu____278 =
      let uu____279 = lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____279
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____280 =
      let uu____281 = FStar_Syntax_Syntax.iarg t_a in
      let uu____282 =
        let uu____284 = FStar_Syntax_Syntax.iarg t_b in
        let uu____285 =
          let uu____287 =
            let uu____288 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____288 in
          let uu____289 =
            let uu____291 =
              let uu____292 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____292 in
            [uu____291] in
          uu____287 :: uu____289 in
        uu____284 :: uu____285 in
      uu____281 :: uu____282 in
    FStar_Syntax_Syntax.mk_Tm_app uu____278 uu____280 in
  uu____277 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair pair unembed_a unembed_b =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____329 = FStar_Syntax_Util.head_and_args pair in
  match uu____329 with
  | (hd1,args) ->
      let uu____357 =
        let uu____365 =
          let uu____366 = FStar_Syntax_Util.un_uinst hd1 in
          uu____366.FStar_Syntax_Syntax.n in
        (uu____365, args) in
      (match uu____357 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____377::uu____378::(a,uu____380)::(b,uu____382)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____424 = unembed_a a in
           let uu____425 = unembed_b b in (uu____424, uu____425)
       | uu____426 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____460 =
        let uu____461 =
          let uu____462 = lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____462
            [FStar_Syntax_Syntax.U_zero] in
        let uu____463 =
          let uu____464 = FStar_Syntax_Syntax.iarg typ in [uu____464] in
        FStar_Syntax_Syntax.mk_Tm_app uu____461 uu____463 in
      uu____460 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____470 =
        let uu____471 =
          let uu____472 = lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____472
            [FStar_Syntax_Syntax.U_zero] in
        let uu____473 =
          let uu____474 = FStar_Syntax_Syntax.iarg typ in
          let uu____475 =
            let uu____477 =
              let uu____478 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____478 in
            [uu____477] in
          uu____474 :: uu____475 in
        FStar_Syntax_Syntax.mk_Tm_app uu____471 uu____473 in
      uu____470 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____501 = FStar_Syntax_Util.head_and_args o in
  match uu____501 with
  | (hd1,args) ->
      let uu____528 =
        let uu____536 =
          let uu____537 = FStar_Syntax_Util.un_uinst hd1 in
          uu____537.FStar_Syntax_Syntax.n in
        (uu____536, args) in
      (match uu____528 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____547) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____559::(a,uu____561)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____587 = unembed_a a in
           FStar_Pervasives_Native.Some uu____587
       | uu____588 -> failwith "Not an embedded option")
let rec embed_list embed_a t_a l =
  match l with
  | [] ->
      let uu____621 =
        let uu____622 =
          let uu____623 = lid_as_data_tm FStar_Parser_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____623
            [FStar_Syntax_Syntax.U_zero] in
        let uu____624 =
          let uu____625 = FStar_Syntax_Syntax.iarg t_a in [uu____625] in
        FStar_Syntax_Syntax.mk_Tm_app uu____622 uu____624 in
      uu____621 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____633 =
        let uu____634 =
          let uu____635 = lid_as_data_tm FStar_Parser_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____635
            [FStar_Syntax_Syntax.U_zero] in
        let uu____636 =
          let uu____637 = FStar_Syntax_Syntax.iarg t_a in
          let uu____638 =
            let uu____640 =
              let uu____641 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____641 in
            let uu____642 =
              let uu____644 =
                let uu____645 = embed_list embed_a t_a tl1 in
                FStar_Syntax_Syntax.as_arg uu____645 in
              [uu____644] in
            uu____640 :: uu____642 in
          uu____637 :: uu____638 in
        FStar_Syntax_Syntax.mk_Tm_app uu____634 uu____636 in
      uu____633 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____669 = FStar_Syntax_Util.head_and_args l1 in
  match uu____669 with
  | (hd1,args) ->
      let uu____696 =
        let uu____704 =
          let uu____705 = FStar_Syntax_Util.un_uinst hd1 in
          uu____705.FStar_Syntax_Syntax.n in
        (uu____704, args) in
      (match uu____696 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____715) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____729)::(tl1,uu____731)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
           let uu____765 = unembed_a hd2 in
           let uu____766 = unembed_list unembed_a tl1 in uu____765 ::
             uu____766
       | uu____768 ->
           let uu____776 =
             let uu____777 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____777 in
           failwith uu____776)
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_binder fstar_tactics_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list unembed_binder t
let embed_env:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    let uu____791 =
      let uu____792 = FStar_TypeChecker_Env.all_binders env in
      embed_list embed_binder fstar_tactics_binder uu____792 in
    protect_embedded_term fstar_tactics_env uu____791
let unembed_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun protected_embedded_env  ->
      let embedded_env = un_protect_embedded_term protected_embedded_env in
      let binders = unembed_list unembed_binder embedded_env in
      FStar_List.fold_left
        (fun env1  ->
           fun b  ->
             let uu____809 =
               FStar_TypeChecker_Env.try_lookup_bv env1
                 (FStar_Pervasives_Native.fst b) in
             match uu____809 with
             | FStar_Pervasives_Native.None  ->
                 FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____819 -> env1) env binders
let embed_term:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term fstar_tactics_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_goal: FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term =
  fun g  ->
    embed_pair
      ((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty))
      embed_env fstar_tactics_env embed_term fstar_tactics_term
let unembed_goal:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun env  ->
    fun t  ->
      let uu____838 = unembed_pair t (unembed_env env) unembed_term in
      match uu____838 with
      | (env1,goal_ty) ->
          {
            FStar_Tactics_Basic.context = env1;
            FStar_Tactics_Basic.witness = FStar_Pervasives_Native.None;
            FStar_Tactics_Basic.goal_ty = goal_ty
          }
let embed_goals:
  FStar_Tactics_Basic.goal Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_goal fstar_tactics_goal l
let unembed_goals:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal Prims.list
  = fun env  -> fun egs  -> unembed_list (unembed_goal env) egs
type state =
  (FStar_Tactics_Basic.goal Prims.list,FStar_Tactics_Basic.goal Prims.list)
    FStar_Pervasives_Native.tuple2
let embed_state: state -> FStar_Syntax_Syntax.term =
  fun s  ->
    embed_pair s embed_goals fstar_tactics_goals embed_goals
      fstar_tactics_goals
let unembed_state:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Tactics_Basic.goal Prims.list,FStar_Tactics_Basic.goal
                                             Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun s  ->
      let s1 = FStar_Syntax_Util.unascribe s in
      unembed_pair s1 (unembed_goals env) (unembed_goals env)
let embed_unit:
  Prims.unit ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun u  -> FStar_Syntax_Util.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____879  -> ()
let embed_bool:
  Prims.bool ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____887 =
      let uu____888 = FStar_Syntax_Subst.compress t in
      uu____888.FStar_Syntax_Syntax.n in
    match uu____887 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____892 -> failwith "Not an embedded bool"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____907)) -> s
    | uu____908 ->
        let uu____909 =
          let uu____910 =
            let uu____911 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____911 ")" in
          Prims.strcat "Not an embedded string (" uu____910 in
        failwith uu____909
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____938 =
        let uu____939 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____940 =
          let uu____941 = FStar_Syntax_Syntax.iarg t_a in
          let uu____942 =
            let uu____944 =
              let uu____945 = embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____945 in
            let uu____946 =
              let uu____948 =
                let uu____949 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____949 in
              [uu____948] in
            uu____944 :: uu____946 in
          uu____941 :: uu____942 in
        FStar_Syntax_Syntax.mk_Tm_app uu____939 uu____940 in
      uu____938 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____958 =
        let uu____959 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____960 =
          let uu____961 = FStar_Syntax_Syntax.iarg t_a in
          let uu____962 =
            let uu____964 =
              let uu____965 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____965 in
            let uu____966 =
              let uu____968 =
                let uu____969 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____969 in
              [uu____968] in
            uu____964 :: uu____966 in
          uu____961 :: uu____962 in
        FStar_Syntax_Syntax.mk_Tm_app uu____959 uu____960 in
      uu____958 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____1005 = FStar_Syntax_Util.head_and_args res1 in
  match uu____1005 with
  | (hd1,args) ->
      let uu____1037 =
        let uu____1045 =
          let uu____1046 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1046.FStar_Syntax_Syntax.n in
        (uu____1045, args) in
      (match uu____1037 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____1063)::(embedded_state,uu____1065)::[]) when
           let uu____1099 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1099 ->
           let uu____1100 =
             let uu____1103 = unembed_a a in
             let uu____1104 = unembed_state env embedded_state in
             (uu____1103, uu____1104) in
           FStar_Util.Inl uu____1100
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____1112)::(embedded_state,uu____1114)::[])
           when
           let uu____1148 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1148 ->
           let uu____1149 =
             let uu____1152 = unembed_string embedded_string in
             let uu____1153 = unembed_state env embedded_state in
             (uu____1152, uu____1153) in
           FStar_Util.Inr uu____1149
       | uu____1158 ->
           let uu____1166 =
             let uu____1167 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____1167 in
           failwith uu____1166)
type formula =
  | Connective of FStar_Syntax_Util.connective
  | App of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term Prims.list)
  FStar_Pervasives_Native.tuple2
  | Name of FStar_Syntax_Syntax.bv
let uu___is_Connective: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Connective _0 -> true | uu____1193 -> false
let __proj__Connective__item___0: formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1208 -> false
let __proj__App__item___0:
  formula ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1229 -> false
let __proj__Name__item___0: formula -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Name _0 -> _0
let embed_formula: formula -> FStar_Syntax_Syntax.term =
  fun f  ->
    let encode_app l args =
      let hd1 =
        if FStar_Ident.lid_equals l FStar_Parser_Const.true_lid
        then fstar_tactics_True_
        else
          if FStar_Ident.lid_equals l FStar_Parser_Const.false_lid
          then fstar_tactics_False_
          else
            if FStar_Ident.lid_equals l FStar_Parser_Const.and_lid
            then fstar_tactics_And
            else
              if FStar_Ident.lid_equals l FStar_Parser_Const.or_lid
              then fstar_tactics_Or
              else
                if FStar_Ident.lid_equals l FStar_Parser_Const.not_lid
                then fstar_tactics_Not
                else
                  if FStar_Ident.lid_equals l FStar_Parser_Const.imp_lid
                  then fstar_tactics_Implies
                  else
                    if FStar_Ident.lid_equals l FStar_Parser_Const.iff_lid
                    then fstar_tactics_Iff
                    else
                      if FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid
                      then fstar_tactics_Eq
                      else
                        (let uu____1256 =
                           let uu____1257 = FStar_Ident.string_of_lid l in
                           Prims.strcat "Unrecognized connective" uu____1257 in
                         failwith uu____1256) in
      match args with
      | [] -> hd1
      | uu____1262 ->
          let uu____1263 =
            let uu____1264 =
              FStar_List.map
                (fun uu____1267  ->
                   match uu____1267 with
                   | (x,uu____1271) ->
                       let uu____1272 = embed_term x in
                       FStar_Syntax_Syntax.as_arg uu____1272) args in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1264 in
          uu____1263 FStar_Pervasives_Native.None FStar_Range.dummyRange in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1280 =
          let uu____1281 =
            let uu____1282 =
              let uu____1283 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1283 in
            let uu____1284 =
              let uu____1286 =
                let uu____1287 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1287 in
              [uu____1286] in
            uu____1282 :: uu____1284 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1281 in
        uu____1280 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1295 =
          let uu____1296 =
            let uu____1297 =
              let uu____1298 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1298 in
            let uu____1299 =
              let uu____1301 =
                let uu____1302 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1302 in
              [uu____1301] in
            uu____1297 :: uu____1299 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1296 in
        uu____1295 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1313 =
          let uu____1314 =
            let uu____1315 =
              let uu____1316 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1316 in
            let uu____1317 =
              let uu____1319 =
                let uu____1320 = embed_list embed_term fstar_tactics_term ts in
                FStar_Syntax_Syntax.as_arg uu____1320 in
              [uu____1319] in
            uu____1315 :: uu____1317 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1314 in
        uu____1313 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Name bv ->
        let uu____1326 =
          let uu____1327 =
            let uu____1328 =
              let uu____1329 =
                let uu____1330 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1330 in
              FStar_Syntax_Syntax.as_arg uu____1329 in
            [uu____1328] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1327 in
        uu____1326 FStar_Pervasives_Native.None FStar_Range.dummyRange
let term_as_formula:
  FStar_Syntax_Syntax.term -> formula FStar_Pervasives_Native.option =
  fun t  ->
    let uu____1340 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1340 with
    | FStar_Pervasives_Native.Some c ->
        FStar_Pervasives_Native.Some (Connective c)
    | uu____1344 ->
        let uu____1346 =
          let uu____1347 = FStar_Syntax_Subst.compress t in
          uu____1347.FStar_Syntax_Syntax.n in
        (match uu____1346 with
         | FStar_Syntax_Syntax.Tm_app uu____1351 ->
             let uu____1361 = FStar_Syntax_Util.head_and_args t in
             (match uu____1361 with
              | (hd1,args) ->
                  let uu____1388 =
                    let uu____1389 =
                      let uu____1393 =
                        FStar_List.map FStar_Pervasives_Native.fst args in
                      (hd1, uu____1393) in
                    App uu____1389 in
                  FStar_Pervasives_Native.Some uu____1388)
         | FStar_Syntax_Syntax.Tm_name bv ->
             FStar_Pervasives_Native.Some (Name bv)
         | uu____1411 -> FStar_Pervasives_Native.None)
type vconst =
  | C_Unit
  | C_Int of Prims.string
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____1419 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____1424 -> false
let __proj__C_Int__item___0: vconst -> Prims.string =
  fun projectee  -> match projectee with | C_Int _0 -> _0
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.binder
  | Tv_FVar of FStar_Syntax_Syntax.fv
  | Tv_App of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | Tv_Abs of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | Tv_Arrow of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | Tv_Type of Prims.unit
  | Tv_Refine of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | Tv_Const of vconst
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____1476 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____1488 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____1502 -> false
let __proj__Tv_App__item___0:
  term_view ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____1522 -> false
let __proj__Tv_Abs__item___0:
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____1542 -> false
let __proj__Tv_Arrow__item___0:
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____1560 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____1574 -> false
let __proj__Tv_Refine__item___0:
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____1592 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____1603 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term fstar_tactics_fvar uu____1603
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____1610 -> failwith "Not an embedded fv"
let embed_const:
  vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | C_Unit  -> tac_C_Unit
    | C_Int s ->
        let uu____1615 =
          let uu____1616 =
            let uu____1617 =
              let uu____1618 = FStar_Syntax_Util.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____1618 in
            [uu____1617] in
          FStar_Syntax_Syntax.mk_Tm_app tac_C_Int uu____1616 in
        uu____1615 FStar_Pervasives_Native.None FStar_Range.dummyRange
let embed_term_view:
  term_view ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t with
    | Tv_FVar fv ->
        let uu____1627 =
          let uu____1628 =
            let uu____1629 =
              let uu____1630 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1630 in
            [uu____1629] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_FVar uu____1628 in
        uu____1627 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Var bv ->
        let uu____1636 =
          let uu____1637 =
            let uu____1638 =
              let uu____1639 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1639 in
            [uu____1638] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Var uu____1637 in
        uu____1636 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_App (hd1,a) ->
        let uu____1646 =
          let uu____1647 =
            let uu____1648 =
              let uu____1649 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1649 in
            let uu____1650 =
              let uu____1652 =
                let uu____1653 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1653 in
              [uu____1652] in
            uu____1648 :: uu____1650 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_App uu____1647 in
        uu____1646 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Abs (b,t1) ->
        let uu____1660 =
          let uu____1661 =
            let uu____1662 =
              let uu____1663 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1663 in
            let uu____1664 =
              let uu____1666 =
                let uu____1667 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1667 in
              [uu____1666] in
            uu____1662 :: uu____1664 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Abs uu____1661 in
        uu____1660 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Arrow (b,t1) ->
        let uu____1674 =
          let uu____1675 =
            let uu____1676 =
              let uu____1677 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1677 in
            let uu____1678 =
              let uu____1680 =
                let uu____1681 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1681 in
              [uu____1680] in
            uu____1676 :: uu____1678 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Arrow uu____1675 in
        uu____1674 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Type u ->
        let uu____1687 =
          let uu____1688 =
            let uu____1689 =
              let uu____1690 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1690 in
            [uu____1689] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Type uu____1688 in
        uu____1687 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Refine (bv,t1) ->
        let uu____1697 =
          let uu____1698 =
            let uu____1699 =
              let uu____1700 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1700 in
            let uu____1701 =
              let uu____1703 =
                let uu____1704 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1704 in
              [uu____1703] in
            uu____1699 :: uu____1701 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Refine uu____1698 in
        uu____1697 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Const c ->
        let uu____1710 =
          let uu____1711 =
            let uu____1712 =
              let uu____1713 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1713 in
            [uu____1712] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Const uu____1711 in
        uu____1710 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1722 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1722 with
    | (hd1,args) ->
        let uu____1748 =
          let uu____1756 =
            let uu____1757 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1757.FStar_Syntax_Syntax.n in
          (uu____1756, args) in
        (match uu____1748 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Unit_lid -> C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1777)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Int_lid ->
             let uu____1795 =
               let uu____1796 = FStar_Syntax_Subst.compress i in
               uu____1796.FStar_Syntax_Syntax.n in
             (match uu____1795 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1800)) -> C_Int s
              | uu____1807 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1808 -> failwith "not an embedded vconst")
let unembed_term_view: FStar_Syntax_Syntax.term -> term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1820 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1820 with
    | (hd1,args) ->
        let uu____1846 =
          let uu____1854 =
            let uu____1855 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1855.FStar_Syntax_Syntax.n in
          (uu____1854, args) in
        (match uu____1846 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1865)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Var_lid ->
             let uu____1883 = unembed_binder b in Tv_Var uu____1883
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1886)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_FVar_lid ->
             let uu____1904 = unembed_fvar b in Tv_FVar uu____1904
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1907)::(r,uu____1909)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_App_lid ->
             let uu____1935 =
               let uu____1938 = unembed_term l in
               let uu____1939 = unembed_term r in (uu____1938, uu____1939) in
             Tv_App uu____1935
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1942)::(t2,uu____1944)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Abs_lid ->
             let uu____1970 =
               let uu____1973 = unembed_binder b in
               let uu____1974 = unembed_term t2 in (uu____1973, uu____1974) in
             Tv_Abs uu____1970
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1977)::(t2,uu____1979)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Arrow_lid ->
             let uu____2005 =
               let uu____2008 = unembed_binder b in
               let uu____2009 = unembed_term t2 in (uu____2008, uu____2009) in
             Tv_Arrow uu____2005
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2012)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Type_lid ->
             (unembed_unit u; Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2033)::(t2,uu____2035)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Refine_lid ->
             let uu____2061 =
               let uu____2064 = unembed_binder b in
               let uu____2065 = unembed_term t2 in (uu____2064, uu____2065) in
             Tv_Refine uu____2061
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2068)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Const_lid ->
             let uu____2086 = unembed_const c in Tv_Const uu____2086
         | uu____2087 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____2105::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____2123 = init xs in x :: uu____2123
let inspectfv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2130 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2130
let packfv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2136 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2136
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspectbv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect:
  FStar_Syntax_Syntax.term -> term_view FStar_Pervasives_Native.option =
  fun t  ->
    let uu____2145 =
      let uu____2146 = FStar_Syntax_Subst.compress t in
      uu____2146.FStar_Syntax_Syntax.n in
    match uu____2145 with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2151 =
          let uu____2152 = FStar_Syntax_Syntax.mk_binder bv in
          Tv_Var uu____2152 in
        FStar_All.pipe_left
          (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____2151
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left
          (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) (Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2187 = last args in
        (match uu____2187 with
         | (a,uu____2198) ->
             let uu____2203 =
               let uu____2204 =
                 let uu____2207 =
                   let uu____2210 =
                     let uu____2211 = init args in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2211 in
                   uu____2210 FStar_Pervasives_Native.None
                     t.FStar_Syntax_Syntax.pos in
                 (uu____2207, a) in
               Tv_App uu____2204 in
             FStar_All.pipe_left
               (fun _0_31  -> FStar_Pervasives_Native.Some _0_31) uu____2203)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2225,uu____2226) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
        let uu____2279 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
        (match uu____2279 with
         | (bs',t2) ->
             let uu____2287 =
               match bs' with
               | b1::bs1 -> (b1, bs1)
               | [] -> failwith "impossible" in
             (match uu____2287 with
              | (b1,bs1) ->
                  let uu____2338 =
                    let uu____2339 =
                      let uu____2342 = FStar_Syntax_Util.abs bs1 t2 k in
                      (b1, uu____2342) in
                    Tv_Abs uu____2339 in
                  FStar_All.pipe_left
                    (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                    uu____2338))
    | FStar_Syntax_Syntax.Tm_type uu____2346 ->
        FStar_All.pipe_left
          (fun _0_33  -> FStar_Pervasives_Native.Some _0_33) (Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
        let uu____2376 = FStar_Syntax_Subst.open_comp [b] k in
        (match uu____2376 with
         | (b',k1) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2398 -> failwith "impossible" in
             let uu____2401 =
               let uu____2402 =
                 let uu____2405 = FStar_Syntax_Util.arrow bs k1 in
                 (b1, uu____2405) in
               Tv_Arrow uu____2402 in
             FStar_All.pipe_left
               (fun _0_34  -> FStar_Pervasives_Native.Some _0_34) uu____2401)
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2420 = FStar_Syntax_Subst.open_term [b] t1 in
        (match uu____2420 with
         | (b',t2) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2438 -> failwith "impossible" in
             FStar_All.pipe_left
               (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
               (Tv_Refine (b1, t2)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> C_Unit
          | FStar_Const.Const_int (s,uu____2447) -> C_Int s
          | uu____2454 -> failwith "unknown constant" in
        FStar_All.pipe_left
          (fun _0_36  -> FStar_Pervasives_Native.Some _0_36) (Tv_Const c1)
    | uu____2456 ->
        (FStar_Util.print_string "inspect: outside of expected syntax\n";
         FStar_Pervasives_Native.None)
let pack: term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | Tv_Var (bv,uu____2462) -> FStar_Syntax_Syntax.bv_to_tm bv
    | Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | Tv_App (l,r) ->
        let uu____2466 =
          let uu____2472 = FStar_Syntax_Syntax.as_arg r in [uu____2472] in
        FStar_Syntax_Util.mk_app l uu____2466
    | Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | Tv_Arrow (b,t) ->
        let uu____2482 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2482
    | Tv_Type () -> FStar_Syntax_Util.ktype
    | Tv_Refine ((bv,uu____2486),t) -> FStar_Syntax_Util.refine bv t
    | Tv_Const (C_Unit ) -> FStar_Syntax_Util.exp_unit
    | Tv_Const (C_Int s) -> FStar_Syntax_Util.exp_int s
    | uu____2491 -> failwith "pack: unexpected term view"
let embed_order: FStar_Tactics_Basic.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Tactics_Basic.Lt  -> ord_Lt
    | FStar_Tactics_Basic.Eq  -> ord_Eq
    | FStar_Tactics_Basic.Gt  -> ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2499 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2499 with
    | (hd1,args) ->
        let uu____2525 =
          let uu____2533 =
            let uu____2534 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2534.FStar_Syntax_Syntax.n in
          (uu____2533, args) in
        (match uu____2525 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
             FStar_Tactics_Basic.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
             FStar_Tactics_Basic.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
             FStar_Tactics_Basic.Gt
         | uu____2572 -> failwith "not an embedded order")