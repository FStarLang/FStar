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
    let uu____225 = FStar_Syntax_Syntax.bv_to_name (Prims.fst b) in
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
            let uu____287 = embed_a (Prims.fst x) in
            FStar_Syntax_Syntax.as_arg uu____287 in
          let uu____288 =
            let uu____290 =
              let uu____291 = embed_b (Prims.snd x) in
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
             let uu____808 =
               FStar_TypeChecker_Env.try_lookup_bv env1 (Prims.fst b) in
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
    (FStar_Syntax_Syntax.mk
       (FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))) None
      FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____911)) -> FStar_Util.string_of_unicode bytes
    | uu____914 ->
        let uu____915 =
          let uu____916 =
            let uu____917 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____917 ")" in
          Prims.strcat "Not an embedded string (" uu____916 in
        failwith uu____915
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____944 =
        let uu____945 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____946 =
          let uu____947 = FStar_Syntax_Syntax.iarg t_a in
          let uu____948 =
            let uu____950 =
              let uu____951 = embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____951 in
            let uu____952 =
              let uu____954 =
                let uu____955 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____955 in
              [uu____954] in
            uu____950 :: uu____952 in
          uu____947 :: uu____948 in
        FStar_Syntax_Syntax.mk_Tm_app uu____945 uu____946 in
      uu____944 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____964 =
        let uu____965 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____966 =
          let uu____967 = FStar_Syntax_Syntax.iarg t_a in
          let uu____968 =
            let uu____970 =
              let uu____971 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____971 in
            let uu____972 =
              let uu____974 =
                let uu____975 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____975 in
              [uu____974] in
            uu____970 :: uu____972 in
          uu____967 :: uu____968 in
        FStar_Syntax_Syntax.mk_Tm_app uu____965 uu____966 in
      uu____964 None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____1011 = FStar_Syntax_Util.head_and_args res1 in
  match uu____1011 with
  | (hd1,args) ->
      let uu____1043 =
        let uu____1051 =
          let uu____1052 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1052.FStar_Syntax_Syntax.n in
        (uu____1051, args) in
      (match uu____1043 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____1069)::(embedded_state,uu____1071)::[]) when
           let uu____1105 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1105 ->
           let uu____1106 =
             let uu____1109 = unembed_a a in
             let uu____1110 = unembed_state env embedded_state in
             (uu____1109, uu____1110) in
           FStar_Util.Inl uu____1106
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____1118)::(embedded_state,uu____1120)::[])
           when
           let uu____1154 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1154 ->
           let uu____1155 =
             let uu____1158 = unembed_string embedded_string in
             let uu____1159 = unembed_state env embedded_state in
             (uu____1158, uu____1159) in
           FStar_Util.Inr uu____1155
       | uu____1164 ->
           let uu____1172 =
             let uu____1173 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____1173 in
           failwith uu____1172)
type formula =
  | Connective of FStar_Syntax_Util.connective
  | App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  | Name of FStar_Syntax_Syntax.bv
let uu___is_Connective: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Connective _0 -> true | uu____1196 -> false
let __proj__Connective__item___0: formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1211 -> false
let __proj__App__item___0:
  formula -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1232 -> false
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
                        (let uu____1259 =
                           let uu____1260 = FStar_Ident.string_of_lid l in
                           Prims.strcat "Unrecognized connective" uu____1260 in
                         failwith uu____1259) in
      match args with
      | [] -> hd1
      | uu____1265 ->
          let uu____1266 =
            let uu____1267 =
              FStar_List.map
                (fun uu____1270  ->
                   match uu____1270 with
                   | (x,uu____1274) ->
                       let uu____1275 = embed_term x in
                       FStar_Syntax_Syntax.as_arg uu____1275) args in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1267 in
          uu____1266 None FStar_Range.dummyRange in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1283 =
          let uu____1284 =
            let uu____1285 =
              let uu____1286 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1286 in
            let uu____1287 =
              let uu____1289 =
                let uu____1290 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1290 in
              [uu____1289] in
            uu____1285 :: uu____1287 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1284 in
        uu____1283 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1298 =
          let uu____1299 =
            let uu____1300 =
              let uu____1301 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1301 in
            let uu____1302 =
              let uu____1304 =
                let uu____1305 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1305 in
              [uu____1304] in
            uu____1300 :: uu____1302 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1299 in
        uu____1298 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1316 =
          let uu____1317 =
            let uu____1318 =
              let uu____1319 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1319 in
            let uu____1320 =
              let uu____1322 =
                let uu____1323 = embed_list embed_term fstar_tactics_term ts in
                FStar_Syntax_Syntax.as_arg uu____1323 in
              [uu____1322] in
            uu____1318 :: uu____1320 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1317 in
        uu____1316 None FStar_Range.dummyRange
    | Name bv ->
        let uu____1329 =
          let uu____1330 =
            let uu____1331 =
              let uu____1332 =
                let uu____1333 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1333 in
              FStar_Syntax_Syntax.as_arg uu____1332 in
            [uu____1331] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1330 in
        uu____1329 None FStar_Range.dummyRange
let term_as_formula: FStar_Syntax_Syntax.term -> formula Prims.option =
  fun t  ->
    let uu____1343 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1343 with
    | Some c -> Some (Connective c)
    | uu____1347 ->
        let uu____1349 =
          let uu____1350 = FStar_Syntax_Subst.compress t in
          uu____1350.FStar_Syntax_Syntax.n in
        (match uu____1349 with
         | FStar_Syntax_Syntax.Tm_app uu____1354 ->
             let uu____1364 = FStar_Syntax_Util.head_and_args t in
             (match uu____1364 with
              | (hd1,args) ->
                  let uu____1391 =
                    let uu____1392 =
                      let uu____1396 = FStar_List.map Prims.fst args in
                      (hd1, uu____1396) in
                    App uu____1392 in
                  Some uu____1391)
         | FStar_Syntax_Syntax.Tm_name bv -> Some (Name bv)
         | uu____1414 -> None)
type vconst =
  | C_Unit
  | C_Int of Prims.string
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____1421 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____1426 -> false
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
    match projectee with | Tv_Var _0 -> true | uu____1470 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____1482 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____1496 -> false
let __proj__Tv_App__item___0:
  term_view -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____1516 -> false
let __proj__Tv_Abs__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____1536 -> false
let __proj__Tv_Arrow__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____1554 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____1568 -> false
let __proj__Tv_Refine__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____1586 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____1597 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term fstar_tactics_fvar uu____1597
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____1604 -> failwith "Not an embedded fv"
let embed_const:
  vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | C_Unit  -> tac_C_Unit
    | C_Int s ->
        let uu____1609 =
          let uu____1610 =
            let uu____1611 =
              let uu____1612 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____1612 in
            [uu____1611] in
          FStar_Syntax_Syntax.mk_Tm_app tac_C_Int uu____1610 in
        uu____1609 None FStar_Range.dummyRange
let embed_term_view:
  term_view ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t with
    | Tv_FVar fv ->
        let uu____1621 =
          let uu____1622 =
            let uu____1623 =
              let uu____1624 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1624 in
            [uu____1623] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_FVar uu____1622 in
        uu____1621 None FStar_Range.dummyRange
    | Tv_Var bv ->
        let uu____1630 =
          let uu____1631 =
            let uu____1632 =
              let uu____1633 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1633 in
            [uu____1632] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Var uu____1631 in
        uu____1630 None FStar_Range.dummyRange
    | Tv_App (hd1,a) ->
        let uu____1640 =
          let uu____1641 =
            let uu____1642 =
              let uu____1643 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1643 in
            let uu____1644 =
              let uu____1646 =
                let uu____1647 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1647 in
              [uu____1646] in
            uu____1642 :: uu____1644 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_App uu____1641 in
        uu____1640 None FStar_Range.dummyRange
    | Tv_Abs (b,t1) ->
        let uu____1654 =
          let uu____1655 =
            let uu____1656 =
              let uu____1657 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1657 in
            let uu____1658 =
              let uu____1660 =
                let uu____1661 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1661 in
              [uu____1660] in
            uu____1656 :: uu____1658 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Abs uu____1655 in
        uu____1654 None FStar_Range.dummyRange
    | Tv_Arrow (b,t1) ->
        let uu____1668 =
          let uu____1669 =
            let uu____1670 =
              let uu____1671 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1671 in
            let uu____1672 =
              let uu____1674 =
                let uu____1675 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1675 in
              [uu____1674] in
            uu____1670 :: uu____1672 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Arrow uu____1669 in
        uu____1668 None FStar_Range.dummyRange
    | Tv_Type u ->
        let uu____1681 =
          let uu____1682 =
            let uu____1683 =
              let uu____1684 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1684 in
            [uu____1683] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Type uu____1682 in
        uu____1681 None FStar_Range.dummyRange
    | Tv_Refine (bv,t1) ->
        let uu____1691 =
          let uu____1692 =
            let uu____1693 =
              let uu____1694 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1694 in
            let uu____1695 =
              let uu____1697 =
                let uu____1698 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1698 in
              [uu____1697] in
            uu____1693 :: uu____1695 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Refine uu____1692 in
        uu____1691 None FStar_Range.dummyRange
    | Tv_Const c ->
        let uu____1704 =
          let uu____1705 =
            let uu____1706 =
              let uu____1707 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1707 in
            [uu____1706] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Const uu____1705 in
        uu____1704 None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1716 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1716 with
    | (hd1,args) ->
        let uu____1742 =
          let uu____1750 =
            let uu____1751 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1751.FStar_Syntax_Syntax.n in
          (uu____1750, args) in
        (match uu____1742 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Unit_lid -> C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1771)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Int_lid ->
             let uu____1789 =
               let uu____1790 = FStar_Syntax_Subst.compress i in
               uu____1790.FStar_Syntax_Syntax.n in
             (match uu____1789 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1794)) -> C_Int s
              | uu____1801 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1802 -> failwith "not an embedded vconst")
let unembed_term_view: FStar_Syntax_Syntax.term -> term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1814 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1814 with
    | (hd1,args) ->
        let uu____1840 =
          let uu____1848 =
            let uu____1849 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1849.FStar_Syntax_Syntax.n in
          (uu____1848, args) in
        (match uu____1840 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1859)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Var_lid ->
             let uu____1877 = unembed_binder b in Tv_Var uu____1877
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1880)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_FVar_lid ->
             let uu____1898 = unembed_fvar b in Tv_FVar uu____1898
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1901)::(r,uu____1903)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_App_lid ->
             let uu____1929 =
               let uu____1932 = unembed_term l in
               let uu____1933 = unembed_term r in (uu____1932, uu____1933) in
             Tv_App uu____1929
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1936)::(t2,uu____1938)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Abs_lid ->
             let uu____1964 =
               let uu____1967 = unembed_binder b in
               let uu____1968 = unembed_term t2 in (uu____1967, uu____1968) in
             Tv_Abs uu____1964
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1971)::(t2,uu____1973)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Arrow_lid ->
             let uu____1999 =
               let uu____2002 = unembed_binder b in
               let uu____2003 = unembed_term t2 in (uu____2002, uu____2003) in
             Tv_Arrow uu____1999
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2006)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Type_lid ->
             (unembed_unit u; Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2027)::(t2,uu____2029)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Refine_lid ->
             let uu____2055 =
               let uu____2058 = unembed_binder b in
               let uu____2059 = unembed_term t2 in (uu____2058, uu____2059) in
             Tv_Refine uu____2055
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2062)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Const_lid ->
             let uu____2080 = unembed_const c in Tv_Const uu____2080
         | uu____2081 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____2099::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____2117 = init xs in x :: uu____2117
let inspectfv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2124 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2124
let packfv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2130 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2130
      FStar_Syntax_Syntax.Delta_equational None
let inspectbv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (Prims.fst b)
let inspect: FStar_Syntax_Syntax.term -> term_view Prims.option =
  fun t  ->
    let uu____2139 =
      let uu____2140 = FStar_Syntax_Subst.compress t in
      uu____2140.FStar_Syntax_Syntax.n in
    match uu____2139 with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2145 =
          let uu____2146 = FStar_Syntax_Syntax.mk_binder bv in
          Tv_Var uu____2146 in
        FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____2145
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left (fun _0_30  -> Some _0_30) (Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2181 = last args in
        (match uu____2181 with
         | (a,uu____2192) ->
             let uu____2197 =
               let uu____2198 =
                 let uu____2201 =
                   let uu____2204 =
                     let uu____2205 = init args in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2205 in
                   uu____2204 None t.FStar_Syntax_Syntax.pos in
                 (uu____2201, a) in
               Tv_App uu____2198 in
             FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____2197)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2219,uu____2220) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
        let uu____2273 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
        (match uu____2273 with
         | (bs',t2) ->
             let uu____2281 =
               match bs' with
               | b1::bs1 -> (b1, bs1)
               | [] -> failwith "impossible" in
             (match uu____2281 with
              | (b1,bs1) ->
                  let uu____2332 =
                    let uu____2333 =
                      let uu____2336 = FStar_Syntax_Util.abs bs1 t2 k in
                      (b1, uu____2336) in
                    Tv_Abs uu____2333 in
                  FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____2332))
    | FStar_Syntax_Syntax.Tm_type uu____2340 ->
        FStar_All.pipe_left (fun _0_33  -> Some _0_33) (Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
        let uu____2370 = FStar_Syntax_Subst.open_comp [b] k in
        (match uu____2370 with
         | (b',k1) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2392 -> failwith "impossible" in
             let uu____2395 =
               let uu____2396 =
                 let uu____2399 = FStar_Syntax_Util.arrow bs k1 in
                 (b1, uu____2399) in
               Tv_Arrow uu____2396 in
             FStar_All.pipe_left (fun _0_34  -> Some _0_34) uu____2395)
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2414 = FStar_Syntax_Subst.open_term [b] t1 in
        (match uu____2414 with
         | (b',t2) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2432 -> failwith "impossible" in
             FStar_All.pipe_left (fun _0_35  -> Some _0_35)
               (Tv_Refine (b1, t2)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> C_Unit
          | FStar_Const.Const_int (s,uu____2441) -> C_Int s
          | uu____2448 -> failwith "unknown constant" in
        FStar_All.pipe_left (fun _0_36  -> Some _0_36) (Tv_Const c1)
    | uu____2450 ->
        (FStar_Util.print_string "inspect: outside of expected syntax\n";
         None)
let pack: term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | Tv_Var (bv,uu____2456) -> FStar_Syntax_Syntax.bv_to_tm bv
    | Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | Tv_App (l,r) ->
        let uu____2460 =
          let uu____2466 = FStar_Syntax_Syntax.as_arg r in [uu____2466] in
        FStar_Syntax_Util.mk_app l uu____2460
    | Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | Tv_Arrow (b,t) ->
        let uu____2476 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2476
    | Tv_Type () -> FStar_Syntax_Util.ktype
    | Tv_Refine ((bv,uu____2480),t) -> FStar_Syntax_Util.refine bv t
    | Tv_Const (C_Unit ) -> FStar_Syntax_Const.exp_unit
    | Tv_Const (C_Int s) -> FStar_Syntax_Const.exp_int s
    | uu____2485 -> failwith "pack: unexpected term view"
let embed_order: FStar_Tactics_Basic.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Tactics_Basic.Lt  -> ord_Lt
    | FStar_Tactics_Basic.Eq  -> ord_Eq
    | FStar_Tactics_Basic.Gt  -> ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2493 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2493 with
    | (hd1,args) ->
        let uu____2519 =
          let uu____2527 =
            let uu____2528 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2528.FStar_Syntax_Syntax.n in
          (uu____2527, args) in
        (match uu____2519 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
             FStar_Tactics_Basic.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
             FStar_Tactics_Basic.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
             FStar_Tactics_Basic.Gt
         | uu____2566 -> failwith "not an embedded order")