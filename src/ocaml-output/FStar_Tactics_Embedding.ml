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
  mk_tactic_lid_as_term "embed"
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
let fstar_tactics_Tv_Var: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_Var"
let fstar_tactics_Tv_FVar: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_FVar"
let fstar_tactics_Tv_App: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_App"
let fstar_tactics_Tv_Abs: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_Abs"
let fstar_tactics_Tv_Arrow: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_Arrow"
let fstar_tactics_Tv_Type: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_Type"
let fstar_tactics_Tv_Refine: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_Refine"
let fstar_tactics_Tv_Const: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Tv_Const"
let fstar_tactics_C_Unit: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "C_Unit"
let fstar_tactics_C_Int: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "C_Int"
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
let rec embed_list l embed_a t_a =
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
                let uu____644 = embed_list tl1 embed_a t_a in
                FStar_Syntax_Syntax.as_arg uu____644 in
              [uu____643] in
            uu____639 :: uu____641 in
          uu____636 :: uu____637 in
        FStar_Syntax_Syntax.mk_Tm_app uu____633 uu____635 in
      uu____632 None FStar_Range.dummyRange
let rec unembed_list l unembed_a =
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
           let uu____765 = unembed_list tl1 unembed_a in uu____764 ::
             uu____765
       | uu____767 ->
           let uu____775 =
             let uu____776 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____776 in
           failwith uu____775)
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list l embed_binder fstar_tactics_binder
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list t unembed_binder
let embed_env:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    let uu____790 =
      let uu____791 = FStar_TypeChecker_Env.all_binders env in
      embed_list uu____791 embed_binder fstar_tactics_binder in
    protect_embedded_term fstar_tactics_env uu____790
let unembed_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun protected_embedded_env  ->
      let embedded_env = un_protect_embedded_term protected_embedded_env in
      let binders = unembed_list embedded_env unembed_binder in
      FStar_List.fold_left
        (fun env1  ->
           fun b  ->
             let uu____812 =
               FStar_TypeChecker_Env.try_lookup_bv env1 (Prims.fst b) in
             match uu____812 with
             | None  -> FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____822 -> env1) env binders
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
      let uu____841 = unembed_pair t (unembed_env env) unembed_term in
      match uu____841 with
      | (env1,goal_ty) ->
          {
            FStar_Tactics_Basic.context = env1;
            FStar_Tactics_Basic.witness = None;
            FStar_Tactics_Basic.goal_ty = goal_ty
          }
let embed_goals:
  FStar_Tactics_Basic.goal Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list l embed_goal fstar_tactics_goal
let unembed_goals:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal Prims.list
  = fun env  -> fun egs  -> unembed_list egs (unembed_goal env)
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
  fun uu____882  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____890 =
      let uu____891 = FStar_Syntax_Subst.compress t in
      uu____891.FStar_Syntax_Syntax.n in
    match uu____890 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____895 -> failwith "Not an embedded bool"
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
        (bytes,uu____915)) -> FStar_Util.string_of_unicode bytes
    | uu____918 -> failwith "Not an embedded string"
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____945 =
        let uu____946 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____947 =
          let uu____948 = FStar_Syntax_Syntax.iarg t_a in
          let uu____949 =
            let uu____951 =
              let uu____952 = embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____952 in
            let uu____953 =
              let uu____955 =
                let uu____956 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____956 in
              [uu____955] in
            uu____951 :: uu____953 in
          uu____948 :: uu____949 in
        FStar_Syntax_Syntax.mk_Tm_app uu____946 uu____947 in
      uu____945 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____965 =
        let uu____966 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____967 =
          let uu____968 = FStar_Syntax_Syntax.iarg t_a in
          let uu____969 =
            let uu____971 =
              let uu____972 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____972 in
            let uu____973 =
              let uu____975 =
                let uu____976 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals)) in
                FStar_Syntax_Syntax.as_arg uu____976 in
              [uu____975] in
            uu____971 :: uu____973 in
          uu____968 :: uu____969 in
        FStar_Syntax_Syntax.mk_Tm_app uu____966 uu____967 in
      uu____965 None FStar_Range.dummyRange
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____1012 = FStar_Syntax_Util.head_and_args res1 in
  match uu____1012 with
  | (hd1,args) ->
      let uu____1044 =
        let uu____1052 =
          let uu____1053 = FStar_Syntax_Util.un_uinst hd1 in
          uu____1053.FStar_Syntax_Syntax.n in
        (uu____1052, args) in
      (match uu____1044 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____1070)::(embedded_state,uu____1072)::[]) when
           let uu____1106 = fstar_tactics_lid "Success" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1106 ->
           let uu____1107 =
             let uu____1110 = unembed_a a in
             let uu____1111 = unembed_state env embedded_state in
             (uu____1110, uu____1111) in
           FStar_Util.Inl uu____1107
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____1119)::(embedded_state,uu____1121)::[])
           when
           let uu____1155 = fstar_tactics_lid "Failed" in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1155 ->
           let uu____1156 =
             let uu____1159 = unembed_string embedded_string in
             let uu____1160 = unembed_state env embedded_state in
             (uu____1159, uu____1160) in
           FStar_Util.Inr uu____1156
       | uu____1165 ->
           let uu____1173 =
             let uu____1174 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____1174 in
           failwith uu____1173)
type formula =
  | Connective of FStar_Syntax_Util.connective
  | App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  | Name of FStar_Syntax_Syntax.bv
let uu___is_Connective: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Connective _0 -> true | uu____1197 -> false
let __proj__Connective__item___0: formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1212 -> false
let __proj__App__item___0:
  formula -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1233 -> false
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
                        (let uu____1260 =
                           let uu____1261 = FStar_Ident.string_of_lid l in
                           Prims.strcat "Unrecognized connective" uu____1261 in
                         failwith uu____1260) in
      match args with
      | [] -> hd1
      | uu____1266 ->
          let uu____1267 =
            let uu____1268 =
              FStar_List.map
                (fun uu____1271  ->
                   match uu____1271 with
                   | (x,uu____1275) ->
                       let uu____1276 = embed_term x in
                       FStar_Syntax_Syntax.as_arg uu____1276) args in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1268 in
          uu____1267 None FStar_Range.dummyRange in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1284 =
          let uu____1285 =
            let uu____1286 =
              let uu____1287 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1287 in
            let uu____1288 =
              let uu____1290 =
                let uu____1291 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1291 in
              [uu____1290] in
            uu____1286 :: uu____1288 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1285 in
        uu____1284 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1299 =
          let uu____1300 =
            let uu____1301 =
              let uu____1302 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1302 in
            let uu____1303 =
              let uu____1305 =
                let uu____1306 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1306 in
              [uu____1305] in
            uu____1301 :: uu____1303 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1300 in
        uu____1299 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1317 =
          let uu____1318 =
            let uu____1319 =
              let uu____1320 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1320 in
            let uu____1321 =
              let uu____1323 =
                let uu____1324 = embed_list ts embed_term fstar_tactics_term in
                FStar_Syntax_Syntax.as_arg uu____1324 in
              [uu____1323] in
            uu____1319 :: uu____1321 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1318 in
        uu____1317 None FStar_Range.dummyRange
    | Name bv ->
        let uu____1330 =
          let uu____1331 =
            let uu____1332 =
              let uu____1333 =
                let uu____1334 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1334 in
              FStar_Syntax_Syntax.as_arg uu____1333 in
            [uu____1332] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1331 in
        uu____1330 None FStar_Range.dummyRange
let term_as_formula: FStar_Syntax_Syntax.term -> formula Prims.option =
  fun t  ->
    let uu____1344 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1344 with
    | Some c -> Some (Connective c)
    | uu____1348 ->
        let uu____1350 =
          let uu____1351 = FStar_Syntax_Subst.compress t in
          uu____1351.FStar_Syntax_Syntax.n in
        (match uu____1350 with
         | FStar_Syntax_Syntax.Tm_app uu____1355 ->
             let uu____1365 = FStar_Syntax_Util.head_and_args t in
             (match uu____1365 with
              | (hd1,args) ->
                  let uu____1392 =
                    let uu____1393 =
                      let uu____1397 = FStar_List.map Prims.fst args in
                      (hd1, uu____1397) in
                    App uu____1393 in
                  Some uu____1392)
         | FStar_Syntax_Syntax.Tm_name bv -> Some (Name bv)
         | uu____1415 -> None)
type vconst =
  | C_Unit
  | C_Int of Prims.string
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____1422 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____1427 -> false
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
    match projectee with | Tv_Var _0 -> true | uu____1471 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____1483 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____1497 -> false
let __proj__Tv_App__item___0:
  term_view -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____1517 -> false
let __proj__Tv_Abs__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____1537 -> false
let __proj__Tv_Arrow__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____1555 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____1569 -> false
let __proj__Tv_Refine__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____1587 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____1598 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term fstar_tactics_fvar uu____1598
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____1605 -> failwith "Not an embedded fv"
let embed_const:
  vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | C_Unit  -> fstar_tactics_C_Unit
    | C_Int s ->
        let uu____1610 =
          let uu____1611 =
            let uu____1612 =
              let uu____1613 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____1613 in
            [uu____1612] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_C_Int uu____1611 in
        uu____1610 None FStar_Range.dummyRange
let embed_term_view:
  term_view ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t with
    | Tv_FVar fv ->
        let uu____1622 =
          let uu____1623 =
            let uu____1624 =
              let uu____1625 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1625 in
            [uu____1624] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_FVar uu____1623 in
        uu____1622 None FStar_Range.dummyRange
    | Tv_Var bv ->
        let uu____1631 =
          let uu____1632 =
            let uu____1633 =
              let uu____1634 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1634 in
            [uu____1633] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_Var uu____1632 in
        uu____1631 None FStar_Range.dummyRange
    | Tv_App (hd1,a) ->
        let uu____1641 =
          let uu____1642 =
            let uu____1643 =
              let uu____1644 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1644 in
            let uu____1645 =
              let uu____1647 =
                let uu____1648 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1648 in
              [uu____1647] in
            uu____1643 :: uu____1645 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_App uu____1642 in
        uu____1641 None FStar_Range.dummyRange
    | Tv_Abs (b,t1) ->
        let uu____1655 =
          let uu____1656 =
            let uu____1657 =
              let uu____1658 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1658 in
            let uu____1659 =
              let uu____1661 =
                let uu____1662 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1662 in
              [uu____1661] in
            uu____1657 :: uu____1659 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_Abs uu____1656 in
        uu____1655 None FStar_Range.dummyRange
    | Tv_Arrow (b,t1) ->
        let uu____1669 =
          let uu____1670 =
            let uu____1671 =
              let uu____1672 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1672 in
            let uu____1673 =
              let uu____1675 =
                let uu____1676 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1676 in
              [uu____1675] in
            uu____1671 :: uu____1673 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_Arrow uu____1670 in
        uu____1669 None FStar_Range.dummyRange
    | Tv_Type u ->
        let uu____1682 =
          let uu____1683 =
            let uu____1684 =
              let uu____1685 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1685 in
            [uu____1684] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_Type uu____1683 in
        uu____1682 None FStar_Range.dummyRange
    | Tv_Refine (bv,t1) ->
        let uu____1692 =
          let uu____1693 =
            let uu____1694 =
              let uu____1695 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1695 in
            let uu____1696 =
              let uu____1698 =
                let uu____1699 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1699 in
              [uu____1698] in
            uu____1694 :: uu____1696 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_Refine uu____1693 in
        uu____1692 None FStar_Range.dummyRange
    | Tv_Const c ->
        let uu____1705 =
          let uu____1706 =
            let uu____1707 =
              let uu____1708 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1708 in
            [uu____1707] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Tv_Const uu____1706 in
        uu____1705 None FStar_Range.dummyRange
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1723::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1741 = init xs in x :: uu____1741
let inspect: FStar_Syntax_Syntax.term -> term_view Prims.option =
  fun t  ->
    (let uu____1749 = FStar_Syntax_Print.term_to_string t in
     FStar_Util.print1 "GGG inspecting %s\n" uu____1749);
    (let uu____1750 =
       let uu____1751 = FStar_Syntax_Subst.compress t in
       uu____1751.FStar_Syntax_Syntax.n in
     match uu____1750 with
     | FStar_Syntax_Syntax.Tm_name bv ->
         FStar_All.pipe_left (fun _0_28  -> Some _0_28) (Tv_Var (bv, None))
     | FStar_Syntax_Syntax.Tm_fvar fv ->
         FStar_All.pipe_left (fun _0_29  -> Some _0_29) (Tv_FVar fv)
     | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
         failwith "inspect: empty arguments on Tm_app"
     | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
         let uu____1791 = last args in
         (match uu____1791 with
          | (a,uu____1802) ->
              let uu____1807 =
                let uu____1808 =
                  let uu____1811 =
                    let uu____1814 =
                      let uu____1815 = init args in
                      FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1815 in
                    uu____1814 None t.FStar_Syntax_Syntax.pos in
                  (uu____1811, a) in
                Tv_App uu____1808 in
              FStar_All.pipe_left (fun _0_30  -> Some _0_30) uu____1807)
     | FStar_Syntax_Syntax.Tm_abs ([],uu____1829,uu____1830) ->
         failwith "inspect: empty arguments on Tm_abs"
     | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
         let uu____1883 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
         (match uu____1883 with
          | (bs',t2) ->
              let uu____1891 =
                match bs' with
                | [] -> failwith "impossible"
                | b1::bs1 -> (b1, bs1) in
              (match uu____1891 with
               | (b1,bs1) ->
                   let uu____1942 =
                     let uu____1943 =
                       let uu____1946 = FStar_Syntax_Util.abs bs1 t2 k in
                       (b1, uu____1946) in
                     Tv_Abs uu____1943 in
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____1942))
     | FStar_Syntax_Syntax.Tm_type uu____1950 ->
         FStar_All.pipe_left (fun _0_32  -> Some _0_32) (Tv_Type ())
     | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
         failwith "inspect: empty binders on arrow"
     | FStar_Syntax_Syntax.Tm_arrow (b::[],k) ->
         let uu____1978 =
           let uu____1979 =
             let uu____1982 =
               let uu____1985 = FStar_Syntax_Util.comp_to_comp_typ k in
               uu____1985.FStar_Syntax_Syntax.result_typ in
             (b, uu____1982) in
           Tv_Arrow uu____1979 in
         FStar_All.pipe_left (fun _0_33  -> Some _0_33) uu____1978
     | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
         let uu____2008 =
           let uu____2009 =
             let uu____2012 = FStar_Syntax_Util.arrow bs k in (b, uu____2012) in
           Tv_Arrow uu____2009 in
         FStar_All.pipe_left (fun _0_34  -> Some _0_34) uu____2008
     | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
         let uu____2026 =
           let uu____2027 =
             let uu____2030 = FStar_Syntax_Syntax.mk_binder b in
             (uu____2030, t1) in
           Tv_Refine uu____2027 in
         FStar_All.pipe_left (fun _0_35  -> Some _0_35) uu____2026
     | FStar_Syntax_Syntax.Tm_constant c ->
         let c1 =
           match c with
           | FStar_Const.Const_unit  -> C_Unit
           | FStar_Const.Const_int (s,uu____2037) -> C_Int s
           | uu____2044 -> failwith "unknown constant" in
         FStar_All.pipe_left (fun _0_36  -> Some _0_36) (Tv_Const c1)
     | uu____2046 ->
         (FStar_Util.print_string "inspect: outside of expected syntax\n";
          None))