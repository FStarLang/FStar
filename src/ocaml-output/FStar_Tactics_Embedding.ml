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
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
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
  lid_as_tm FStar_Syntax_Const.fstar_tactics_embed_lid
let fstar_tactics_term_view: FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "term_view"
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
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
  FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2")
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
      uu____28 None x.FStar_Syntax_Syntax.pos
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
               FStar_Syntax_Const.fstar_tactics_embed_lid
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
               FStar_Syntax_Const.fstar_tactics_embed_lid
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
    | Unembed_failed uu____213 -> true
    | uu____214 -> false
let __proj__Unembed_failed__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Unembed_failed uu____221 -> uu____221
let embed_binder:
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    let uu____225 = FStar_Syntax_Syntax.bv_to_name (fst b) in
    protect_embedded_term fstar_tactics_binder uu____225
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____232 -> failwith "Not an embedded binder"
let embed_pair x embed_a t_a embed_b t_b =
  let uu____276 =
    let uu____277 =
      let uu____278 = lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____278
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____279 =
      let uu____280 = FStar_Syntax_Syntax.iarg t_a in
      let uu____281 =
        let uu____283 = FStar_Syntax_Syntax.iarg t_b in
        let uu____284 =
          let uu____286 =
            let uu____287 = embed_a (fst x) in
            FStar_Syntax_Syntax.as_arg uu____287 in
          let uu____288 =
            let uu____290 =
              let uu____291 = embed_b (snd x) in
              FStar_Syntax_Syntax.as_arg uu____291 in
            [uu____290] in
          uu____286 :: uu____288 in
        uu____283 :: uu____284 in
      uu____280 :: uu____281 in
    FStar_Syntax_Syntax.mk_Tm_app uu____277 uu____279 in
  uu____276 None FStar_Range.dummyRange
let unembed_pair pair unembed_a unembed_b =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____328 = FStar_Syntax_Util.head_and_args pair in
  match uu____328 with
  | (hd1,args) ->
      let uu____356 =
        let uu____364 =
          let uu____365 = FStar_Syntax_Util.un_uinst hd1 in
          uu____365.FStar_Syntax_Syntax.n in
        (uu____364, args) in
      (match uu____356 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____376::uu____377::(a,uu____379)::(b,uu____381)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____423 = unembed_a a in
           let uu____424 = unembed_b b in (uu____423, uu____424)
       | uu____425 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____459 =
        let uu____460 =
          let uu____461 = lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____461
            [FStar_Syntax_Syntax.U_zero] in
        let uu____462 =
          let uu____463 = FStar_Syntax_Syntax.iarg typ in [uu____463] in
        FStar_Syntax_Syntax.mk_Tm_app uu____460 uu____462 in
      uu____459 None FStar_Range.dummyRange
  | Some a ->
      let uu____469 =
        let uu____470 =
          let uu____471 = lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____471
            [FStar_Syntax_Syntax.U_zero] in
        let uu____472 =
          let uu____473 = FStar_Syntax_Syntax.iarg typ in
          let uu____474 =
            let uu____476 =
              let uu____477 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____477 in
            [uu____476] in
          uu____473 :: uu____474 in
        FStar_Syntax_Syntax.mk_Tm_app uu____470 uu____472 in
      uu____469 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____500 = FStar_Syntax_Util.head_and_args o in
  match uu____500 with
  | (hd1,args) ->
      let uu____527 =
        let uu____535 =
          let uu____536 = FStar_Syntax_Util.un_uinst hd1 in
          uu____536.FStar_Syntax_Syntax.n in
        (uu____535, args) in
      (match uu____527 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____546) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____558::(a,uu____560)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____586 = unembed_a a in Some uu____586
       | uu____587 -> failwith "Not an embedded option")
let rec embed_list embed_a t_a l =
  match l with
  | [] ->
      let uu____620 =
        let uu____621 =
          let uu____622 = lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____622
            [FStar_Syntax_Syntax.U_zero] in
        let uu____623 =
          let uu____624 = FStar_Syntax_Syntax.iarg t_a in [uu____624] in
        FStar_Syntax_Syntax.mk_Tm_app uu____621 uu____623 in
      uu____620 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____632 =
        let uu____633 =
          let uu____634 = lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____634
            [FStar_Syntax_Syntax.U_zero] in
        let uu____635 =
          let uu____636 = FStar_Syntax_Syntax.iarg t_a in
          let uu____637 =
            let uu____639 =
              let uu____640 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____640 in
            let uu____641 =
              let uu____643 =
                let uu____644 = embed_list embed_a t_a tl1 in
                FStar_Syntax_Syntax.as_arg uu____644 in
              [uu____643] in
            uu____639 :: uu____641 in
          uu____636 :: uu____637 in
        FStar_Syntax_Syntax.mk_Tm_app uu____633 uu____635 in
      uu____632 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____668 = FStar_Syntax_Util.head_and_args l1 in
  match uu____668 with
  | (hd1,args) ->
      let uu____695 =
        let uu____703 =
          let uu____704 = FStar_Syntax_Util.un_uinst hd1 in
          uu____704.FStar_Syntax_Syntax.n in
        (uu____703, args) in
      (match uu____695 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____714) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____728)::(tl1,uu____730)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____764 = unembed_a hd2 in
           let uu____765 = unembed_list unembed_a tl1 in uu____764 ::
             uu____765
       | uu____767 ->
           let uu____775 =
             let uu____776 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____776 in
           failwith uu____775)
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
    let uu____790 =
      let uu____791 = FStar_TypeChecker_Env.all_binders env in
      embed_list embed_binder fstar_tactics_binder uu____791 in
    protect_embedded_term fstar_tactics_env uu____790
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
             let uu____808 = FStar_TypeChecker_Env.try_lookup_bv env1 (fst b) in
             match uu____808 with
             | None  -> FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____818 -> env1) env binders
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
      let uu____837 = unembed_pair t (unembed_env env) unembed_term in
      match uu____837 with
      | (env1,goal_ty) ->
          {
            FStar_Tactics_Basic.context = env1;
            FStar_Tactics_Basic.witness = None;
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
  (FStar_Tactics_Basic.goal Prims.list* FStar_Tactics_Basic.goal Prims.list)
let embed_state: state -> FStar_Syntax_Syntax.term =
  fun s  ->
    embed_pair s embed_goals fstar_tactics_goals embed_goals
      fstar_tactics_goals
let unembed_state:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Tactics_Basic.goal Prims.list* FStar_Tactics_Basic.goal
        Prims.list)
  =
  fun env  ->
    fun s  ->
      let s1 = FStar_Syntax_Util.unascribe s in
      unembed_pair s1 (unembed_goals env) (unembed_goals env)
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____878  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____886 =
      let uu____887 = FStar_Syntax_Subst.compress t in
      uu____887.FStar_Syntax_Syntax.n in
    match uu____886 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____891 -> failwith "Not an embedded bool"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange))) None
      FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____907)) -> FStar_Util.string_of_unicode bytes
    | uu____910 ->
        let uu____911 =
          let uu____912 =
            let uu____913 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____913 ")" in
          Prims.strcat "Not an embedded string (" uu____912 in
        failwith uu____911
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____940 =
        let uu____941 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____942 =
          let uu____943 = FStar_Syntax_Syntax.iarg t_a in
          let uu____944 =
            let uu____946 =
              let uu____947 = embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____947 in
            let uu____948 =
              let uu____950 =
                let uu____951 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____951 in
              [uu____950] in
            uu____946 :: uu____948 in
          uu____943 :: uu____944 in
        FStar_Syntax_Syntax.mk_Tm_app uu____941 uu____942 in
      uu____940 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____960 =
        let uu____961 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____962 =
          let uu____963 = FStar_Syntax_Syntax.iarg t_a in
          let uu____964 =
            let uu____966 =
              let uu____967 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____967 in
            let uu____968 =
              let uu____970 =
                let uu____971 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____971 in
              [uu____970] in
            uu____966 :: uu____968 in
          uu____963 :: uu____964 in
        FStar_Syntax_Syntax.mk_Tm_app uu____961 uu____962 in
      uu____960 None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____1007 = FStar_Syntax_Util.head_and_args res1 in
  match uu____1007 with
  | (hd1,args) ->
      let uu____1039 =
        let uu____1047 =
          let uu____1048 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1048.FStar_Syntax_Syntax.n in
        (uu____1047, args) in
      (match uu____1039 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____1065)::(embedded_state,uu____1067)::[]) when
           let uu____1101 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1101 ->
           let uu____1102 =
             let uu____1105 = unembed_a a in
             let uu____1106 = unembed_state env embedded_state in
             (uu____1105, uu____1106) in
           FStar_Util.Inl uu____1102
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____1114)::(embedded_state,uu____1116)::[])
           when
           let uu____1150 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1150 ->
           let uu____1151 =
             let uu____1154 = unembed_string embedded_string in
             let uu____1155 = unembed_state env embedded_state in
             (uu____1154, uu____1155) in
           FStar_Util.Inr uu____1151
       | uu____1160 ->
           let uu____1168 =
             let uu____1169 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____1169 in
           failwith uu____1168)
type formula =
  | Connective of FStar_Syntax_Util.connective
  | App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  | Name of FStar_Syntax_Syntax.bv
let uu___is_Connective: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Connective _0 -> true | uu____1192 -> false
let __proj__Connective__item___0: formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1207 -> false
let __proj__App__item___0:
  formula -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1228 -> false
let __proj__Name__item___0: formula -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Name _0 -> _0
let embed_formula: formula -> FStar_Syntax_Syntax.term =
  fun f  ->
    let encode_app l args =
      let hd1 =
        if FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid
        then fstar_tactics_True_
        else
          if FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid
          then fstar_tactics_False_
          else
            if FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid
            then fstar_tactics_And
            else
              if FStar_Ident.lid_equals l FStar_Syntax_Const.or_lid
              then fstar_tactics_Or
              else
                if FStar_Ident.lid_equals l FStar_Syntax_Const.not_lid
                then fstar_tactics_Not
                else
                  if FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid
                  then fstar_tactics_Implies
                  else
                    if FStar_Ident.lid_equals l FStar_Syntax_Const.iff_lid
                    then fstar_tactics_Iff
                    else
                      if FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid
                      then fstar_tactics_Eq
                      else
                        (let uu____1255 =
                           let uu____1256 = FStar_Ident.string_of_lid l in
                           Prims.strcat "Unrecognized connective" uu____1256 in
                         failwith uu____1255) in
      match args with
      | [] -> hd1
      | uu____1261 ->
          let uu____1262 =
            let uu____1263 =
              FStar_List.map
                (fun uu____1266  ->
                   match uu____1266 with
                   | (x,uu____1270) ->
                       let uu____1271 = embed_term x in
                       FStar_Syntax_Syntax.as_arg uu____1271) args in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1263 in
          uu____1262 None FStar_Range.dummyRange in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1279 =
          let uu____1280 =
            let uu____1281 =
              let uu____1282 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1282 in
            let uu____1283 =
              let uu____1285 =
                let uu____1286 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1286 in
              [uu____1285] in
            uu____1281 :: uu____1283 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1280 in
        uu____1279 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1294 =
          let uu____1295 =
            let uu____1296 =
              let uu____1297 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1297 in
            let uu____1298 =
              let uu____1300 =
                let uu____1301 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1301 in
              [uu____1300] in
            uu____1296 :: uu____1298 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1295 in
        uu____1294 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1312 =
          let uu____1313 =
            let uu____1314 =
              let uu____1315 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1315 in
            let uu____1316 =
              let uu____1318 =
                let uu____1319 = embed_list embed_term fstar_tactics_term ts in
                FStar_Syntax_Syntax.as_arg uu____1319 in
              [uu____1318] in
            uu____1314 :: uu____1316 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1313 in
        uu____1312 None FStar_Range.dummyRange
    | Name bv ->
        let uu____1325 =
          let uu____1326 =
            let uu____1327 =
              let uu____1328 =
                let uu____1329 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1329 in
              FStar_Syntax_Syntax.as_arg uu____1328 in
            [uu____1327] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1326 in
        uu____1325 None FStar_Range.dummyRange
let term_as_formula: FStar_Syntax_Syntax.term -> formula option =
  fun t  ->
    let uu____1339 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1339 with
    | Some c -> Some (Connective c)
    | uu____1343 ->
        let uu____1345 =
          let uu____1346 = FStar_Syntax_Subst.compress t in
          uu____1346.FStar_Syntax_Syntax.n in
        (match uu____1345 with
         | FStar_Syntax_Syntax.Tm_app uu____1350 ->
             let uu____1360 = FStar_Syntax_Util.head_and_args t in
             (match uu____1360 with
              | (hd1,args) ->
                  let uu____1387 =
                    let uu____1388 =
                      let uu____1392 =
                        FStar_List.map FStar_Pervasives.fst args in
                      (hd1, uu____1392) in
                    App uu____1388 in
                  Some uu____1387)
         | FStar_Syntax_Syntax.Tm_name bv -> Some (Name bv)
         | uu____1410 -> None)
type vconst =
  | C_Unit
  | C_Int of Prims.string
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____1417 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____1422 -> false
let __proj__C_Int__item___0: vconst -> Prims.string =
  fun projectee  -> match projectee with | C_Int _0 -> _0
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.binder
  | Tv_FVar of FStar_Syntax_Syntax.fv
  | Tv_App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  | Tv_Abs of (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term)
  | Tv_Arrow of (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term)
  | Tv_Type of Prims.unit
  | Tv_Refine of (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term)
  | Tv_Const of vconst
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____1466 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____1478 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____1492 -> false
let __proj__Tv_App__item___0:
  term_view -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____1512 -> false
let __proj__Tv_Abs__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____1532 -> false
let __proj__Tv_Arrow__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____1550 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____1564 -> false
let __proj__Tv_Refine__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____1582 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____1593 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term fstar_tactics_fvar uu____1593
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____1600 -> failwith "Not an embedded fv"
let embed_const:
  vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | C_Unit  -> tac_C_Unit
    | C_Int s ->
        let uu____1605 =
          let uu____1606 =
            let uu____1607 =
              let uu____1608 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____1608 in
            [uu____1607] in
          FStar_Syntax_Syntax.mk_Tm_app tac_C_Int uu____1606 in
        uu____1605 None FStar_Range.dummyRange
let embed_term_view:
  term_view ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t with
    | Tv_FVar fv ->
        let uu____1617 =
          let uu____1618 =
            let uu____1619 =
              let uu____1620 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1620 in
            [uu____1619] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_FVar uu____1618 in
        uu____1617 None FStar_Range.dummyRange
    | Tv_Var bv ->
        let uu____1626 =
          let uu____1627 =
            let uu____1628 =
              let uu____1629 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1629 in
            [uu____1628] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Var uu____1627 in
        uu____1626 None FStar_Range.dummyRange
    | Tv_App (hd1,a) ->
        let uu____1636 =
          let uu____1637 =
            let uu____1638 =
              let uu____1639 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1639 in
            let uu____1640 =
              let uu____1642 =
                let uu____1643 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1643 in
              [uu____1642] in
            uu____1638 :: uu____1640 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_App uu____1637 in
        uu____1636 None FStar_Range.dummyRange
    | Tv_Abs (b,t1) ->
        let uu____1650 =
          let uu____1651 =
            let uu____1652 =
              let uu____1653 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1653 in
            let uu____1654 =
              let uu____1656 =
                let uu____1657 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1657 in
              [uu____1656] in
            uu____1652 :: uu____1654 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Abs uu____1651 in
        uu____1650 None FStar_Range.dummyRange
    | Tv_Arrow (b,t1) ->
        let uu____1664 =
          let uu____1665 =
            let uu____1666 =
              let uu____1667 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1667 in
            let uu____1668 =
              let uu____1670 =
                let uu____1671 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1671 in
              [uu____1670] in
            uu____1666 :: uu____1668 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Arrow uu____1665 in
        uu____1664 None FStar_Range.dummyRange
    | Tv_Type u ->
        let uu____1677 =
          let uu____1678 =
            let uu____1679 =
              let uu____1680 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1680 in
            [uu____1679] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Type uu____1678 in
        uu____1677 None FStar_Range.dummyRange
    | Tv_Refine (bv,t1) ->
        let uu____1687 =
          let uu____1688 =
            let uu____1689 =
              let uu____1690 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1690 in
            let uu____1691 =
              let uu____1693 =
                let uu____1694 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1694 in
              [uu____1693] in
            uu____1689 :: uu____1691 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Refine uu____1688 in
        uu____1687 None FStar_Range.dummyRange
    | Tv_Const c ->
        let uu____1700 =
          let uu____1701 =
            let uu____1702 =
              let uu____1703 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1703 in
            [uu____1702] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Const uu____1701 in
        uu____1700 None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1712 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1712 with
    | (hd1,args) ->
        let uu____1738 =
          let uu____1746 =
            let uu____1747 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1747.FStar_Syntax_Syntax.n in
          (uu____1746, args) in
        (match uu____1738 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Unit_lid -> C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1767)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Int_lid ->
             let uu____1785 =
               let uu____1786 = FStar_Syntax_Subst.compress i in
               uu____1786.FStar_Syntax_Syntax.n in
             (match uu____1785 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1790)) -> C_Int s
              | uu____1797 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1798 -> failwith "not an embedded vconst")
let unembed_term_view: FStar_Syntax_Syntax.term -> term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1810 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1810 with
    | (hd1,args) ->
        let uu____1836 =
          let uu____1844 =
            let uu____1845 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1845.FStar_Syntax_Syntax.n in
          (uu____1844, args) in
        (match uu____1836 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1855)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Var_lid ->
             let uu____1873 = unembed_binder b in Tv_Var uu____1873
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1876)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_FVar_lid ->
             let uu____1894 = unembed_fvar b in Tv_FVar uu____1894
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1897)::(r,uu____1899)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_App_lid ->
             let uu____1925 =
               let uu____1928 = unembed_term l in
               let uu____1929 = unembed_term r in (uu____1928, uu____1929) in
             Tv_App uu____1925
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1932)::(t2,uu____1934)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Abs_lid ->
             let uu____1960 =
               let uu____1963 = unembed_binder b in
               let uu____1964 = unembed_term t2 in (uu____1963, uu____1964) in
             Tv_Abs uu____1960
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1967)::(t2,uu____1969)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Arrow_lid ->
             let uu____1995 =
               let uu____1998 = unembed_binder b in
               let uu____1999 = unembed_term t2 in (uu____1998, uu____1999) in
             Tv_Arrow uu____1995
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2002)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Type_lid ->
             (unembed_unit u; Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2023)::(t2,uu____2025)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Refine_lid ->
             let uu____2051 =
               let uu____2054 = unembed_binder b in
               let uu____2055 = unembed_term t2 in (uu____2054, uu____2055) in
             Tv_Refine uu____2051
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2058)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Const_lid ->
             let uu____2076 = unembed_const c in Tv_Const uu____2076
         | uu____2077 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____2095::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____2113 = init xs in x :: uu____2113
let inspectfv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2120 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2120
let packfv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2126 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2126
      FStar_Syntax_Syntax.Delta_equational None
let inspectbv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> term_view option =
  fun t  ->
    let uu____2135 =
      let uu____2136 = FStar_Syntax_Subst.compress t in
      uu____2136.FStar_Syntax_Syntax.n in
    match uu____2135 with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2141 =
          let uu____2142 = FStar_Syntax_Syntax.mk_binder bv in
          Tv_Var uu____2142 in
        FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____2141
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left (fun _0_30  -> Some _0_30) (Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2177 = last args in
        (match uu____2177 with
         | (a,uu____2188) ->
             let uu____2193 =
               let uu____2194 =
                 let uu____2197 =
                   let uu____2200 =
                     let uu____2201 = init args in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2201 in
                   uu____2200 None t.FStar_Syntax_Syntax.pos in
                 (uu____2197, a) in
               Tv_App uu____2194 in
             FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____2193)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2215,uu____2216) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
        let uu____2269 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
        (match uu____2269 with
         | (bs',t2) ->
             let uu____2277 =
               match bs' with
               | b1::bs1 -> (b1, bs1)
               | [] -> failwith "impossible" in
             (match uu____2277 with
              | (b1,bs1) ->
                  let uu____2328 =
                    let uu____2329 =
                      let uu____2332 = FStar_Syntax_Util.abs bs1 t2 k in
                      (b1, uu____2332) in
                    Tv_Abs uu____2329 in
                  FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____2328))
    | FStar_Syntax_Syntax.Tm_type uu____2336 ->
        FStar_All.pipe_left (fun _0_33  -> Some _0_33) (Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
        let uu____2366 = FStar_Syntax_Subst.open_comp [b] k in
        (match uu____2366 with
         | (b',k1) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2388 -> failwith "impossible" in
             let uu____2391 =
               let uu____2392 =
                 let uu____2395 = FStar_Syntax_Util.arrow bs k1 in
                 (b1, uu____2395) in
               Tv_Arrow uu____2392 in
             FStar_All.pipe_left (fun _0_34  -> Some _0_34) uu____2391)
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2410 = FStar_Syntax_Subst.open_term [b] t1 in
        (match uu____2410 with
         | (b',t2) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2428 -> failwith "impossible" in
             FStar_All.pipe_left (fun _0_35  -> Some _0_35)
               (Tv_Refine (b1, t2)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> C_Unit
          | FStar_Const.Const_int (s,uu____2437) -> C_Int s
          | uu____2444 -> failwith "unknown constant" in
        FStar_All.pipe_left (fun _0_36  -> Some _0_36) (Tv_Const c1)
    | uu____2446 ->
        (FStar_Util.print_string "inspect: outside of expected syntax\n";
         None)
let pack: term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | Tv_Var (bv,uu____2452) -> FStar_Syntax_Syntax.bv_to_tm bv
    | Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | Tv_App (l,r) ->
        let uu____2456 =
          let uu____2462 = FStar_Syntax_Syntax.as_arg r in [uu____2462] in
        FStar_Syntax_Util.mk_app l uu____2456
    | Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | Tv_Arrow (b,t) ->
        let uu____2472 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2472
    | Tv_Type () -> FStar_Syntax_Util.ktype
    | Tv_Refine ((bv,uu____2476),t) -> FStar_Syntax_Util.refine bv t
    | Tv_Const (C_Unit ) -> FStar_Syntax_Const.exp_unit
    | Tv_Const (C_Int s) -> FStar_Syntax_Const.exp_int s
    | uu____2481 -> failwith "pack: unexpected term view"
let embed_order: FStar_Tactics_Basic.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Tactics_Basic.Lt  -> ord_Lt
    | FStar_Tactics_Basic.Eq  -> ord_Eq
    | FStar_Tactics_Basic.Gt  -> ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2489 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2489 with
    | (hd1,args) ->
        let uu____2515 =
          let uu____2523 =
            let uu____2524 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2524.FStar_Syntax_Syntax.n in
          (uu____2523, args) in
        (match uu____2515 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
             FStar_Tactics_Basic.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
             FStar_Tactics_Basic.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
             FStar_Tactics_Basic.Gt
         | uu____2562 -> failwith "not an embedded order")