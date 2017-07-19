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
      let uu____30 =
        let uu____31 =
          let uu____32 = FStar_Syntax_Syntax.iarg t in
          let uu____33 =
            let uu____36 = FStar_Syntax_Syntax.as_arg x in [uu____36] in
          uu____32 :: uu____33 in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_embed uu____31 in
      uu____30 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
let type_of_embedded: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ =
  fun t  ->
    let uu____42 = FStar_Syntax_Util.head_and_args t in
    match uu____42 with
    | (head1,args) ->
        let uu____91 =
          let uu____106 =
            let uu____107 = FStar_Syntax_Util.un_uinst head1 in
            uu____107.FStar_Syntax_Syntax.n in
          (uu____106, args) in
        (match uu____91 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t1,uu____124)::uu____125::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_tactics_embed_lid
             -> t1
         | uu____176 ->
             let uu____191 =
               let uu____192 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term (1): %s"
                 uu____192 in
             failwith uu____191)
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____196 = FStar_Syntax_Util.head_and_args t in
    match uu____196 with
    | (head1,args) ->
        let uu____245 =
          let uu____260 =
            let uu____261 = FStar_Syntax_Util.un_uinst head1 in
            uu____261.FStar_Syntax_Syntax.n in
          (uu____260, args) in
        (match uu____245 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____277::(x,uu____279)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_tactics_embed_lid
             -> x
         | uu____330 ->
             let uu____345 =
               let uu____346 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term (2): %s"
                 uu____346 in
             failwith uu____345)
exception Unembed_failed of Prims.string
let uu___is_Unembed_failed: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unembed_failed uu____353 -> true
    | uu____354 -> false
let __proj__Unembed_failed__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Unembed_failed uu____361 -> uu____361
let embed_binder:
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    let uu____365 =
      FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b) in
    protect_embedded_term fstar_tactics_binder uu____365
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____372 -> failwith "Not an embedded binder"
let embed_pair x embed_a t_a embed_b t_b =
  let uu____420 =
    let uu____421 =
      let uu____422 = lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____422
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____423 =
      let uu____424 = FStar_Syntax_Syntax.iarg t_a in
      let uu____425 =
        let uu____428 = FStar_Syntax_Syntax.iarg t_b in
        let uu____429 =
          let uu____432 =
            let uu____433 = embed_a (FStar_Pervasives_Native.fst x) in
            FStar_Syntax_Syntax.as_arg uu____433 in
          let uu____434 =
            let uu____437 =
              let uu____438 = embed_b (FStar_Pervasives_Native.snd x) in
              FStar_Syntax_Syntax.as_arg uu____438 in
            [uu____437] in
          uu____432 :: uu____434 in
        uu____428 :: uu____429 in
      uu____424 :: uu____425 in
    FStar_Syntax_Syntax.mk_Tm_app uu____421 uu____423 in
  uu____420 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_pair pair unembed_a unembed_b =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____475 = FStar_Syntax_Util.head_and_args pair in
  match uu____475 with
  | (hd1,args) ->
      let uu____528 =
        let uu____543 =
          let uu____544 = FStar_Syntax_Util.un_uinst hd1 in
          uu____544.FStar_Syntax_Syntax.n in
        (uu____543, args) in
      (match uu____528 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____564::uu____565::(a,uu____567)::(b,uu____569)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____652 = unembed_a a in
           let uu____653 = unembed_b b in (uu____652, uu____653)
       | uu____654 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | FStar_Pervasives_Native.None  ->
      let uu____699 =
        let uu____700 =
          let uu____701 = lid_as_data_tm FStar_Parser_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____701
            [FStar_Syntax_Syntax.U_zero] in
        let uu____702 =
          let uu____703 = FStar_Syntax_Syntax.iarg typ in [uu____703] in
        FStar_Syntax_Syntax.mk_Tm_app uu____700 uu____702 in
      uu____699 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Pervasives_Native.Some a ->
      let uu____707 =
        let uu____708 =
          let uu____709 = lid_as_data_tm FStar_Parser_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____709
            [FStar_Syntax_Syntax.U_zero] in
        let uu____710 =
          let uu____711 = FStar_Syntax_Syntax.iarg typ in
          let uu____712 =
            let uu____715 =
              let uu____716 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____716 in
            [uu____715] in
          uu____711 :: uu____712 in
        FStar_Syntax_Syntax.mk_Tm_app uu____708 uu____710 in
      uu____707 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____738 = FStar_Syntax_Util.head_and_args o in
  match uu____738 with
  | (hd1,args) ->
      let uu____789 =
        let uu____804 =
          let uu____805 = FStar_Syntax_Util.un_uinst hd1 in
          uu____805.FStar_Syntax_Syntax.n in
        (uu____804, args) in
      (match uu____789 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____823) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid ->
           FStar_Pervasives_Native.None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____845::(a,uu____847)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid ->
           let uu____898 = unembed_a a in
           FStar_Pervasives_Native.Some uu____898
       | uu____899 -> failwith "Not an embedded option")
let rec embed_list embed_a t_a l =
  match l with
  | [] ->
      let uu____942 =
        let uu____943 =
          let uu____944 = lid_as_data_tm FStar_Parser_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____944
            [FStar_Syntax_Syntax.U_zero] in
        let uu____945 =
          let uu____946 = FStar_Syntax_Syntax.iarg t_a in [uu____946] in
        FStar_Syntax_Syntax.mk_Tm_app uu____943 uu____945 in
      uu____942 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____953 =
        let uu____954 =
          let uu____955 = lid_as_data_tm FStar_Parser_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____955
            [FStar_Syntax_Syntax.U_zero] in
        let uu____956 =
          let uu____957 = FStar_Syntax_Syntax.iarg t_a in
          let uu____958 =
            let uu____961 =
              let uu____962 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____962 in
            let uu____963 =
              let uu____966 =
                let uu____967 = embed_list embed_a t_a tl1 in
                FStar_Syntax_Syntax.as_arg uu____967 in
              [uu____966] in
            uu____961 :: uu____963 in
          uu____957 :: uu____958 in
        FStar_Syntax_Syntax.mk_Tm_app uu____954 uu____956 in
      uu____953 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____990 = FStar_Syntax_Util.head_and_args l1 in
  match uu____990 with
  | (hd1,args) ->
      let uu____1041 =
        let uu____1056 =
          let uu____1057 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1057.FStar_Syntax_Syntax.n in
        (uu____1056, args) in
      (match uu____1041 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1075) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____1099)::(tl1,uu____1101)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
           let uu____1168 = unembed_a hd2 in
           let uu____1169 = unembed_list unembed_a tl1 in uu____1168 ::
             uu____1169
       | uu____1172 ->
           let uu____1187 =
             let uu____1188 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____1188 in
           failwith uu____1187)
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
    let uu____1206 =
      let uu____1207 = FStar_TypeChecker_Env.all_binders env in
      embed_list embed_binder fstar_tactics_binder uu____1207 in
    protect_embedded_term fstar_tactics_env uu____1206
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
             let uu____1230 =
               FStar_TypeChecker_Env.try_lookup_bv env1
                 (FStar_Pervasives_Native.fst b) in
             match uu____1230 with
             | FStar_Pervasives_Native.None  ->
                 FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____1249 -> env1) env binders
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
      let uu____1271 = unembed_pair t (unembed_env env) unembed_term in
      match uu____1271 with
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
  fun uu____1326  -> ()
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
    let uu____1334 =
      let uu____1335 = FStar_Syntax_Subst.compress t in
      uu____1335.FStar_Syntax_Syntax.n in
    match uu____1334 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____1341 -> failwith "Not an embedded bool"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____1355)) -> FStar_Util.string_of_unicode bytes
    | uu____1360 ->
        let uu____1361 =
          let uu____1362 =
            let uu____1363 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____1363 ")" in
          Prims.strcat "Not an embedded string (" uu____1362 in
        failwith uu____1361
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____1392 =
        let uu____1393 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____1394 =
          let uu____1395 = FStar_Syntax_Syntax.iarg t_a in
          let uu____1396 =
            let uu____1399 =
              let uu____1400 = embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____1400 in
            let uu____1401 =
              let uu____1404 =
                let uu____1405 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____1405 in
              [uu____1404] in
            uu____1399 :: uu____1401 in
          uu____1395 :: uu____1396 in
        FStar_Syntax_Syntax.mk_Tm_app uu____1393 uu____1394 in
      uu____1392 FStar_Pervasives_Native.None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____1414 =
        let uu____1415 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____1416 =
          let uu____1417 = FStar_Syntax_Syntax.iarg t_a in
          let uu____1418 =
            let uu____1421 =
              let uu____1422 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____1422 in
            let uu____1423 =
              let uu____1426 =
                let uu____1427 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____1427 in
              [uu____1426] in
            uu____1421 :: uu____1423 in
          uu____1417 :: uu____1418 in
        FStar_Syntax_Syntax.mk_Tm_app uu____1415 uu____1416 in
      uu____1414 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____1469 = FStar_Syntax_Util.head_and_args res1 in
  match uu____1469 with
  | (hd1,args) ->
      let uu____1530 =
        let uu____1545 =
          let uu____1546 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1546.FStar_Syntax_Syntax.n in
        (uu____1545, args) in
      (match uu____1530 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____1576)::(embedded_state,uu____1578)::[]) when
           let uu____1645 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1645 ->
           let uu____1646 =
             let uu____1651 = unembed_a a in
             let uu____1652 = unembed_state env embedded_state in
             (uu____1651, uu____1652) in
           FStar_Util.Inl uu____1646
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____1664)::(embedded_state,uu____1666)::[])
           when
           let uu____1733 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1733 ->
           let uu____1734 =
             let uu____1739 = unembed_string embedded_string in
             let uu____1740 = unembed_state env embedded_state in
             (uu____1739, uu____1740) in
           FStar_Util.Inr uu____1734
       | uu____1749 ->
           let uu____1764 =
             let uu____1765 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____1765 in
           failwith uu____1764)
type formula =
  | Connective of FStar_Syntax_Util.connective
  | App of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term Prims.list)
  FStar_Pervasives_Native.tuple2
  | Name of FStar_Syntax_Syntax.bv
let uu___is_Connective: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Connective _0 -> true | uu____1800 -> false
let __proj__Connective__item___0: formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1818 -> false
let __proj__App__item___0:
  formula ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1848 -> false
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
                        (let uu____1875 =
                           let uu____1876 = FStar_Ident.string_of_lid l in
                           Prims.strcat "Unrecognized connective" uu____1876 in
                         failwith uu____1875) in
      match args with
      | [] -> hd1
      | uu____1885 ->
          let uu____1886 =
            let uu____1887 =
              FStar_List.map
                (fun uu____1892  ->
                   match uu____1892 with
                   | (x,uu____1898) ->
                       let uu____1899 = embed_term x in
                       FStar_Syntax_Syntax.as_arg uu____1899) args in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1887 in
          uu____1886 FStar_Pervasives_Native.None FStar_Range.dummyRange in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1905 =
          let uu____1906 =
            let uu____1907 =
              let uu____1908 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1908 in
            let uu____1909 =
              let uu____1912 =
                let uu____1913 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1913 in
              [uu____1912] in
            uu____1907 :: uu____1909 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1906 in
        uu____1905 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1919 =
          let uu____1920 =
            let uu____1921 =
              let uu____1922 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1922 in
            let uu____1923 =
              let uu____1926 =
                let uu____1927 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1927 in
              [uu____1926] in
            uu____1921 :: uu____1923 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1920 in
        uu____1919 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1938 =
          let uu____1939 =
            let uu____1940 =
              let uu____1941 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1941 in
            let uu____1942 =
              let uu____1945 =
                let uu____1946 = embed_list embed_term fstar_tactics_term ts in
                FStar_Syntax_Syntax.as_arg uu____1946 in
              [uu____1945] in
            uu____1940 :: uu____1942 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1939 in
        uu____1938 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Name bv ->
        let uu____1950 =
          let uu____1951 =
            let uu____1952 =
              let uu____1953 =
                let uu____1954 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1954 in
              FStar_Syntax_Syntax.as_arg uu____1953 in
            [uu____1952] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1951 in
        uu____1950 FStar_Pervasives_Native.None FStar_Range.dummyRange
let term_as_formula:
  FStar_Syntax_Syntax.term -> formula FStar_Pervasives_Native.option =
  fun t  ->
    let uu____1964 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1964 with
    | FStar_Pervasives_Native.Some c ->
        FStar_Pervasives_Native.Some (Connective c)
    | uu____1970 ->
        let uu____1973 =
          let uu____1974 = FStar_Syntax_Subst.compress t in
          uu____1974.FStar_Syntax_Syntax.n in
        (match uu____1973 with
         | FStar_Syntax_Syntax.Tm_app uu____1981 ->
             let uu____2000 = FStar_Syntax_Util.head_and_args t in
             (match uu____2000 with
              | (hd1,args) ->
                  let uu____2051 =
                    let uu____2052 =
                      let uu____2059 =
                        FStar_List.map FStar_Pervasives_Native.fst args in
                      (hd1, uu____2059) in
                    App uu____2052 in
                  FStar_Pervasives_Native.Some uu____2051)
         | FStar_Syntax_Syntax.Tm_name bv ->
             FStar_Pervasives_Native.Some (Name bv)
         | uu____2093 -> FStar_Pervasives_Native.None)
type vconst =
  | C_Unit
  | C_Int of Prims.string
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____2101 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____2106 -> false
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
    match projectee with | Tv_Var _0 -> true | uu____2166 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____2178 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____2194 -> false
let __proj__Tv_App__item___0:
  term_view ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____2222 -> false
let __proj__Tv_Abs__item___0:
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____2250 -> false
let __proj__Tv_Arrow__item___0:
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____2274 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____2290 -> false
let __proj__Tv_Refine__item___0:
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____2314 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____2325 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term fstar_tactics_fvar uu____2325
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____2332 -> failwith "Not an embedded fv"
let embed_const:
  vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | C_Unit  -> tac_C_Unit
    | C_Int s ->
        let uu____2337 =
          let uu____2338 =
            let uu____2339 =
              let uu____2340 = FStar_Syntax_Util.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____2340 in
            [uu____2339] in
          FStar_Syntax_Syntax.mk_Tm_app tac_C_Int uu____2338 in
        uu____2337 FStar_Pervasives_Native.None FStar_Range.dummyRange
let embed_term_view:
  term_view ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t with
    | Tv_FVar fv ->
        let uu____2347 =
          let uu____2348 =
            let uu____2349 =
              let uu____2350 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____2350 in
            [uu____2349] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_FVar uu____2348 in
        uu____2347 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Var bv ->
        let uu____2354 =
          let uu____2355 =
            let uu____2356 =
              let uu____2357 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____2357 in
            [uu____2356] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Var uu____2355 in
        uu____2354 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_App (hd1,a) ->
        let uu____2362 =
          let uu____2363 =
            let uu____2364 =
              let uu____2365 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____2365 in
            let uu____2366 =
              let uu____2369 =
                let uu____2370 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____2370 in
              [uu____2369] in
            uu____2364 :: uu____2366 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_App uu____2363 in
        uu____2362 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Abs (b,t1) ->
        let uu____2375 =
          let uu____2376 =
            let uu____2377 =
              let uu____2378 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____2378 in
            let uu____2379 =
              let uu____2382 =
                let uu____2383 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____2383 in
              [uu____2382] in
            uu____2377 :: uu____2379 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Abs uu____2376 in
        uu____2375 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Arrow (b,t1) ->
        let uu____2388 =
          let uu____2389 =
            let uu____2390 =
              let uu____2391 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____2391 in
            let uu____2392 =
              let uu____2395 =
                let uu____2396 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____2396 in
              [uu____2395] in
            uu____2390 :: uu____2392 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Arrow uu____2389 in
        uu____2388 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Type u ->
        let uu____2400 =
          let uu____2401 =
            let uu____2402 =
              let uu____2403 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____2403 in
            [uu____2402] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Type uu____2401 in
        uu____2400 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Refine (bv,t1) ->
        let uu____2408 =
          let uu____2409 =
            let uu____2410 =
              let uu____2411 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____2411 in
            let uu____2412 =
              let uu____2415 =
                let uu____2416 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____2416 in
              [uu____2415] in
            uu____2410 :: uu____2412 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Refine uu____2409 in
        uu____2408 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | Tv_Const c ->
        let uu____2420 =
          let uu____2421 =
            let uu____2422 =
              let uu____2423 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____2423 in
            [uu____2422] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Const uu____2421 in
        uu____2420 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2430 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2430 with
    | (hd1,args) ->
        let uu____2479 =
          let uu____2494 =
            let uu____2495 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2495.FStar_Syntax_Syntax.n in
          (uu____2494, args) in
        (match uu____2479 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Unit_lid -> C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____2531)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Int_lid ->
             let uu____2566 =
               let uu____2567 = FStar_Syntax_Subst.compress i in
               uu____2567.FStar_Syntax_Syntax.n in
             (match uu____2566 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____2573)) -> C_Int s
              | uu____2586 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____2587 -> failwith "not an embedded vconst")
let unembed_term_view: FStar_Syntax_Syntax.term -> term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2606 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2606 with
    | (hd1,args) ->
        let uu____2655 =
          let uu____2670 =
            let uu____2671 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2671.FStar_Syntax_Syntax.n in
          (uu____2670, args) in
        (match uu____2655 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2688)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Var_lid ->
             let uu____2723 = unembed_binder b in Tv_Var uu____2723
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____2726)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_FVar_lid ->
             let uu____2761 = unembed_fvar b in Tv_FVar uu____2761
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____2764)::(r,uu____2766)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_App_lid ->
             let uu____2817 =
               let uu____2822 = unembed_term l in
               let uu____2823 = unembed_term r in (uu____2822, uu____2823) in
             Tv_App uu____2817
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2826)::(t2,uu____2828)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Abs_lid ->
             let uu____2879 =
               let uu____2884 = unembed_binder b in
               let uu____2885 = unembed_term t2 in (uu____2884, uu____2885) in
             Tv_Abs uu____2879
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2888)::(t2,uu____2890)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Arrow_lid ->
             let uu____2941 =
               let uu____2946 = unembed_binder b in
               let uu____2947 = unembed_term t2 in (uu____2946, uu____2947) in
             Tv_Arrow uu____2941
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2950)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Type_lid ->
             (unembed_unit u; Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2988)::(t2,uu____2990)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Refine_lid ->
             let uu____3041 =
               let uu____3046 = unembed_binder b in
               let uu____3047 = unembed_term t2 in (uu____3046, uu____3047) in
             Tv_Refine uu____3041
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____3050)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Const_lid ->
             let uu____3085 = unembed_const c in Tv_Const uu____3085
         | uu____3086 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____3113::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____3137 = init xs in x :: uu____3137
let inspectfv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____3147 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____3147
let packfv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____3155 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____3155
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspectbv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect:
  FStar_Syntax_Syntax.term -> term_view FStar_Pervasives_Native.option =
  fun t  ->
    let uu____3166 =
      let uu____3167 = FStar_Syntax_Subst.compress t in
      uu____3167.FStar_Syntax_Syntax.n in
    match uu____3166 with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____3175 =
          let uu____3176 = FStar_Syntax_Syntax.mk_binder bv in
          Tv_Var uu____3176 in
        FStar_All.pipe_left
          (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____3175
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left
          (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) (Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____3241 = last args in
        (match uu____3241 with
         | (a,uu____3261) ->
             let uu____3270 =
               let uu____3271 =
                 let uu____3276 =
                   let uu____3281 =
                     let uu____3282 = init args in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____3282 in
                   uu____3281 FStar_Pervasives_Native.None
                     t.FStar_Syntax_Syntax.pos in
                 (uu____3276, a) in
               Tv_App uu____3271 in
             FStar_All.pipe_left
               (fun _0_31  -> FStar_Pervasives_Native.Some _0_31) uu____3270)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____3303,uu____3304) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
        let uu____3405 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
        (match uu____3405 with
         | (bs',t2) ->
             let uu____3418 =
               match bs' with
               | b1::bs1 -> (b1, bs1)
               | [] -> failwith "impossible" in
             (match uu____3418 with
              | (b1,bs1) ->
                  let uu____3515 =
                    let uu____3516 =
                      let uu____3521 = FStar_Syntax_Util.abs bs1 t2 k in
                      (b1, uu____3521) in
                    Tv_Abs uu____3516 in
                  FStar_All.pipe_left
                    (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                    uu____3515))
    | FStar_Syntax_Syntax.Tm_type uu____3528 ->
        FStar_All.pipe_left
          (fun _0_33  -> FStar_Pervasives_Native.Some _0_33) (Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
        let uu____3583 = FStar_Syntax_Subst.open_comp [b] k in
        (match uu____3583 with
         | (b',k1) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____3622 -> failwith "impossible" in
             let uu____3627 =
               let uu____3628 =
                 let uu____3633 = FStar_Syntax_Util.arrow bs k1 in
                 (b1, uu____3633) in
               Tv_Arrow uu____3628 in
             FStar_All.pipe_left
               (fun _0_34  -> FStar_Pervasives_Native.Some _0_34) uu____3627)
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____3659 = FStar_Syntax_Subst.open_term [b] t1 in
        (match uu____3659 with
         | (b',t2) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____3690 -> failwith "impossible" in
             FStar_All.pipe_left
               (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
               (Tv_Refine (b1, t2)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> C_Unit
          | FStar_Const.Const_int (s,uu____3704) -> C_Int s
          | uu____3717 -> failwith "unknown constant" in
        FStar_All.pipe_left
          (fun _0_36  -> FStar_Pervasives_Native.Some _0_36) (Tv_Const c1)
    | uu____3720 ->
        (FStar_Util.print_string "inspect: outside of expected syntax\n";
         FStar_Pervasives_Native.None)
let pack: term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | Tv_Var (bv,uu____3726) -> FStar_Syntax_Syntax.bv_to_tm bv
    | Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | Tv_App (l,r) ->
        let uu____3730 =
          let uu____3741 = FStar_Syntax_Syntax.as_arg r in [uu____3741] in
        FStar_Syntax_Util.mk_app l uu____3730
    | Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | Tv_Arrow (b,t) ->
        let uu____3756 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____3756
    | Tv_Type () -> FStar_Syntax_Util.ktype
    | Tv_Refine ((bv,uu____3762),t) -> FStar_Syntax_Util.refine bv t
    | Tv_Const (C_Unit ) -> FStar_Syntax_Util.exp_unit
    | Tv_Const (C_Int s) -> FStar_Syntax_Util.exp_int s
    | uu____3769 -> failwith "pack: unexpected term view"
let embed_order: FStar_Tactics_Basic.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Tactics_Basic.Lt  -> ord_Lt
    | FStar_Tactics_Basic.Eq  -> ord_Eq
    | FStar_Tactics_Basic.Gt  -> ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3777 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3777 with
    | (hd1,args) ->
        let uu____3826 =
          let uu____3841 =
            let uu____3842 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3842.FStar_Syntax_Syntax.n in
          (uu____3841, args) in
        (match uu____3826 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
             FStar_Tactics_Basic.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
             FStar_Tactics_Basic.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
             FStar_Tactics_Basic.Gt
         | uu____3914 -> failwith "not an embedded order")