open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid' s
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____11 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
    FStar_All.pipe_right uu____11 FStar_Syntax_Syntax.fv_to_tm
let mk_tactic_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____16 = fstar_tactics_lid' ["Effect"; s] in lid_as_tm uu____16
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____21 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____21
let fstar_tactics_lid_as_data_tm: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____26 = fstar_tactics_lid' ["Effect"; s] in
    lid_as_data_tm uu____26
let fstar_tactics_Failed: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success: FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Success"
let pair_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____37 =
        let uu____38 =
          let uu____39 = lid_as_tm FStar_Reflection_Basic.lid_tuple2 in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____39
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
        let uu____40 =
          let uu____41 = FStar_Syntax_Syntax.as_arg t in
          let uu____42 =
            let uu____44 = FStar_Syntax_Syntax.as_arg s in [uu____44] in
          uu____41 :: uu____42 in
        FStar_Syntax_Syntax.mk_Tm_app uu____38 uu____40 in
      uu____37 None FStar_Range.dummyRange
let embed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun env  -> FStar_Syntax_Util.mk_alien env "tactics_embed_env" None
let unembed_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
<<<<<<< HEAD
  fun env  ->
    fun protected_embedded_env  ->
      let embedded_env = un_protect_embedded_term protected_embedded_env in
      let binders = unembed_list unembed_binder embedded_env in
      FStar_List.fold_left
        (fun env1  ->
           fun b  ->
             let uu____812 = FStar_TypeChecker_Env.try_lookup_bv env1 (fst b) in
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
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange))) None
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
    match projectee with | Connective _0 -> true | uu____1199 -> false
let __proj__Connective__item___0: formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1214 -> false
let __proj__App__item___0:
  formula -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term Prims.list)
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1235 -> false
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
                        (let uu____1262 =
                           let uu____1263 = FStar_Ident.string_of_lid l in
                           Prims.strcat "Unrecognized connective" uu____1263 in
                         failwith uu____1262) in
      match args with
      | [] -> hd1
      | uu____1268 ->
          let uu____1269 =
            let uu____1270 =
              FStar_List.map
                (fun uu____1277  ->
                   match uu____1277 with
                   | (x,uu____1281) ->
                       let uu____1282 = embed_term x in
                       FStar_Syntax_Syntax.as_arg uu____1282) args in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1270 in
          uu____1269 None FStar_Range.dummyRange in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1290 =
          let uu____1291 =
            let uu____1292 =
              let uu____1293 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1293 in
            let uu____1294 =
              let uu____1296 =
                let uu____1297 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1297 in
              [uu____1296] in
            uu____1292 :: uu____1294 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1291 in
        uu____1290 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1305 =
          let uu____1306 =
            let uu____1307 =
              let uu____1308 = embed_binders binders in
              FStar_Syntax_Syntax.as_arg uu____1308 in
            let uu____1309 =
              let uu____1311 =
                let uu____1312 = embed_term typ in
                FStar_Syntax_Syntax.as_arg uu____1312 in
              [uu____1311] in
            uu____1307 :: uu____1309 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1306 in
        uu____1305 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1323 =
          let uu____1324 =
            let uu____1325 =
              let uu____1326 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1326 in
            let uu____1327 =
              let uu____1329 =
                let uu____1330 = embed_list embed_term fstar_tactics_term ts in
                FStar_Syntax_Syntax.as_arg uu____1330 in
              [uu____1329] in
            uu____1325 :: uu____1327 in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1324 in
        uu____1323 None FStar_Range.dummyRange
    | Name bv ->
        let uu____1336 =
          let uu____1337 =
            let uu____1338 =
              let uu____1339 =
                let uu____1340 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____1340 in
              FStar_Syntax_Syntax.as_arg uu____1339 in
            [uu____1338] in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1337 in
        uu____1336 None FStar_Range.dummyRange
let term_as_formula: FStar_Syntax_Syntax.term -> formula option =
  fun t  ->
    let uu____1350 = FStar_Syntax_Util.destruct_typ_as_formula t in
    match uu____1350 with
    | Some c -> Some (Connective c)
    | uu____1354 ->
        let uu____1356 =
          let uu____1357 = FStar_Syntax_Subst.compress t in
          uu____1357.FStar_Syntax_Syntax.n in
        (match uu____1356 with
         | FStar_Syntax_Syntax.Tm_app uu____1361 ->
             let uu____1371 = FStar_Syntax_Util.head_and_args t in
             (match uu____1371 with
              | (hd1,args) ->
                  let uu____1398 =
                    let uu____1399 =
                      let uu____1403 =
                        FStar_List.map FStar_Pervasives.fst args in
                      (hd1, uu____1403) in
                    App uu____1399 in
                  Some uu____1398)
         | FStar_Syntax_Syntax.Tm_name bv -> Some (Name bv)
         | uu____1421 -> None)
type vconst =
  | C_Unit
  | C_Int of Prims.string
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____1429 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____1434 -> false
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
    match projectee with | Tv_Var _0 -> true | uu____1486 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____1498 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____1512 -> false
let __proj__Tv_App__item___0:
  term_view -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____1532 -> false
let __proj__Tv_Abs__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____1552 -> false
let __proj__Tv_Arrow__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____1570 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____1584 -> false
let __proj__Tv_Refine__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____1602 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____1613 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term fstar_tactics_fvar uu____1613
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____1620 -> failwith "Not an embedded fv"
let embed_const:
  vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | C_Unit  -> tac_C_Unit
    | C_Int s ->
        let uu____1625 =
          let uu____1626 =
            let uu____1627 =
              let uu____1628 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____1628 in
            [uu____1627] in
          FStar_Syntax_Syntax.mk_Tm_app tac_C_Int uu____1626 in
        uu____1625 None FStar_Range.dummyRange
let embed_term_view:
  term_view ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t with
    | Tv_FVar fv ->
        let uu____1637 =
          let uu____1638 =
            let uu____1639 =
              let uu____1640 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____1640 in
            [uu____1639] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_FVar uu____1638 in
        uu____1637 None FStar_Range.dummyRange
    | Tv_Var bv ->
        let uu____1646 =
          let uu____1647 =
            let uu____1648 =
              let uu____1649 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1649 in
            [uu____1648] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Var uu____1647 in
        uu____1646 None FStar_Range.dummyRange
    | Tv_App (hd1,a) ->
        let uu____1656 =
          let uu____1657 =
            let uu____1658 =
              let uu____1659 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____1659 in
            let uu____1660 =
              let uu____1662 =
                let uu____1663 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____1663 in
              [uu____1662] in
            uu____1658 :: uu____1660 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_App uu____1657 in
        uu____1656 None FStar_Range.dummyRange
    | Tv_Abs (b,t1) ->
        let uu____1670 =
          let uu____1671 =
            let uu____1672 =
              let uu____1673 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1673 in
            let uu____1674 =
              let uu____1676 =
                let uu____1677 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1677 in
              [uu____1676] in
            uu____1672 :: uu____1674 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Abs uu____1671 in
        uu____1670 None FStar_Range.dummyRange
    | Tv_Arrow (b,t1) ->
        let uu____1684 =
          let uu____1685 =
            let uu____1686 =
              let uu____1687 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____1687 in
            let uu____1688 =
              let uu____1690 =
                let uu____1691 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1691 in
              [uu____1690] in
            uu____1686 :: uu____1688 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Arrow uu____1685 in
        uu____1684 None FStar_Range.dummyRange
    | Tv_Type u ->
        let uu____1697 =
          let uu____1698 =
            let uu____1699 =
              let uu____1700 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____1700 in
            [uu____1699] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Type uu____1698 in
        uu____1697 None FStar_Range.dummyRange
    | Tv_Refine (bv,t1) ->
        let uu____1707 =
          let uu____1708 =
            let uu____1709 =
              let uu____1710 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____1710 in
            let uu____1711 =
              let uu____1713 =
                let uu____1714 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____1714 in
              [uu____1713] in
            uu____1709 :: uu____1711 in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Refine uu____1708 in
        uu____1707 None FStar_Range.dummyRange
    | Tv_Const c ->
        let uu____1720 =
          let uu____1721 =
            let uu____1722 =
              let uu____1723 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____1723 in
            [uu____1722] in
          FStar_Syntax_Syntax.mk_Tm_app tac_Tv_Const uu____1721 in
        uu____1720 None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1732 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1732 with
    | (hd1,args) ->
        let uu____1758 =
          let uu____1766 =
            let uu____1767 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1767.FStar_Syntax_Syntax.n in
          (uu____1766, args) in
        (match uu____1758 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Unit_lid -> C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1787)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_C_Int_lid ->
             let uu____1805 =
               let uu____1806 = FStar_Syntax_Subst.compress i in
               uu____1806.FStar_Syntax_Syntax.n in
             (match uu____1805 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____1810)) -> C_Int s
              | uu____1817 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____1818 -> failwith "not an embedded vconst")
let unembed_term_view: FStar_Syntax_Syntax.term -> term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1830 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1830 with
    | (hd1,args) ->
        let uu____1856 =
          let uu____1864 =
            let uu____1865 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1865.FStar_Syntax_Syntax.n in
          (uu____1864, args) in
        (match uu____1856 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1875)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Var_lid ->
             let uu____1893 = unembed_binder b in Tv_Var uu____1893
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1896)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_FVar_lid ->
             let uu____1914 = unembed_fvar b in Tv_FVar uu____1914
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1917)::(r,uu____1919)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_App_lid ->
             let uu____1945 =
               let uu____1948 = unembed_term l in
               let uu____1949 = unembed_term r in (uu____1948, uu____1949) in
             Tv_App uu____1945
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1952)::(t2,uu____1954)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Abs_lid ->
             let uu____1980 =
               let uu____1983 = unembed_binder b in
               let uu____1984 = unembed_term t2 in (uu____1983, uu____1984) in
             Tv_Abs uu____1980
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1987)::(t2,uu____1989)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Arrow_lid ->
             let uu____2015 =
               let uu____2018 = unembed_binder b in
               let uu____2019 = unembed_term t2 in (uu____2018, uu____2019) in
             Tv_Arrow uu____2015
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____2022)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Type_lid ->
             (unembed_unit u; Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____2043)::(t2,uu____2045)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Refine_lid ->
             let uu____2071 =
               let uu____2074 = unembed_binder b in
               let uu____2075 = unembed_term t2 in (uu____2074, uu____2075) in
             Tv_Refine uu____2071
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____2078)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv tac_Tv_Const_lid ->
             let uu____2096 = unembed_const c in Tv_Const uu____2096
         | uu____2097 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____2115::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____2133 = init xs in x :: uu____2133
let inspectfv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2140 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____2140
let packfv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2146 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____2146
      FStar_Syntax_Syntax.Delta_equational None
let inspectbv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> term_view option =
  fun t  ->
    let uu____2155 =
      let uu____2156 = FStar_Syntax_Subst.compress t in
      uu____2156.FStar_Syntax_Syntax.n in
    match uu____2155 with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2161 =
          let uu____2162 = FStar_Syntax_Syntax.mk_binder bv in
          Tv_Var uu____2162 in
        FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____2161
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left (fun _0_30  -> Some _0_30) (Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2197 = last args in
        (match uu____2197 with
         | (a,uu____2208) ->
             let uu____2213 =
               let uu____2214 =
                 let uu____2217 =
                   let uu____2220 =
                     let uu____2221 = init args in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2221 in
                   uu____2220 None t.FStar_Syntax_Syntax.pos in
                 (uu____2217, a) in
               Tv_App uu____2214 in
             FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____2213)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2235,uu____2236) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs,t1,k) ->
        let uu____2289 = FStar_Syntax_Subst.open_term (b :: bs) t1 in
        (match uu____2289 with
         | (bs',t2) ->
             let uu____2297 =
               match bs' with
               | b1::bs1 -> (b1, bs1)
               | [] -> failwith "impossible" in
             (match uu____2297 with
              | (b1,bs1) ->
                  let uu____2348 =
                    let uu____2349 =
                      let uu____2352 = FStar_Syntax_Util.abs bs1 t2 k in
                      (b1, uu____2352) in
                    Tv_Abs uu____2349 in
                  FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____2348))
    | FStar_Syntax_Syntax.Tm_type uu____2356 ->
        FStar_All.pipe_left (fun _0_33  -> Some _0_33) (Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,k) ->
        let uu____2386 = FStar_Syntax_Subst.open_comp [b] k in
        (match uu____2386 with
         | (b',k1) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2408 -> failwith "impossible" in
             let uu____2411 =
               let uu____2412 =
                 let uu____2415 = FStar_Syntax_Util.arrow bs k1 in
                 (b1, uu____2415) in
               Tv_Arrow uu____2412 in
             FStar_All.pipe_left (fun _0_34  -> Some _0_34) uu____2411)
    | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____2430 = FStar_Syntax_Subst.open_term [b] t1 in
        (match uu____2430 with
         | (b',t2) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2448 -> failwith "impossible" in
             FStar_All.pipe_left (fun _0_35  -> Some _0_35)
               (Tv_Refine (b1, t2)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> C_Unit
          | FStar_Const.Const_int (s,uu____2457) -> C_Int s
          | uu____2464 -> failwith "unknown constant" in
        FStar_All.pipe_left (fun _0_36  -> Some _0_36) (Tv_Const c1)
    | uu____2466 ->
        (FStar_Util.print_string "inspect: outside of expected syntax\n";
         None)
let pack: term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | Tv_Var (bv,uu____2472) -> FStar_Syntax_Syntax.bv_to_tm bv
    | Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | Tv_App (l,r) ->
        let uu____2476 =
          let uu____2482 = FStar_Syntax_Syntax.as_arg r in [uu____2482] in
        FStar_Syntax_Util.mk_app l uu____2476
    | Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | Tv_Arrow (b,t) ->
        let uu____2492 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____2492
    | Tv_Type () -> FStar_Syntax_Util.ktype
    | Tv_Refine ((bv,uu____2496),t) -> FStar_Syntax_Util.refine bv t
    | Tv_Const (C_Unit ) -> FStar_Syntax_Const.exp_unit
    | Tv_Const (C_Int s) -> FStar_Syntax_Const.exp_int s
    | uu____2501 -> failwith "pack: unexpected term view"
let embed_order: FStar_Tactics_Basic.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Tactics_Basic.Lt  -> ord_Lt
    | FStar_Tactics_Basic.Eq  -> ord_Eq
    | FStar_Tactics_Basic.Gt  -> ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2509 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2509 with
    | (hd1,args) ->
        let uu____2535 =
          let uu____2543 =
            let uu____2544 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2544.FStar_Syntax_Syntax.n in
          (uu____2543, args) in
        (match uu____2535 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
             FStar_Tactics_Basic.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
             FStar_Tactics_Basic.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
             FStar_Tactics_Basic.Gt
         | uu____2582 -> failwith "not an embedded order")
=======
  fun ps  ->
    fun t  ->
      let uu____65 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____65 FStar_Dyn.undyn
let embed_proofstate:
  FStar_Tactics_Basic.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  -> FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate" None
let unembed_proofstate:
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.proofstate
  =
  fun ps  ->
    fun t  ->
      let uu____78 = FStar_Syntax_Util.un_alien t in
      FStar_All.pipe_right uu____78 FStar_Dyn.undyn
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____115 =
        let uu____116 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero] in
        let uu____117 =
          let uu____118 = FStar_Syntax_Syntax.iarg t_a in
          let uu____119 =
            let uu____121 =
              let uu____122 = FStar_Reflection_Basic.embed_string msg in
              FStar_Syntax_Syntax.as_arg uu____122 in
            let uu____123 =
              let uu____125 =
                let uu____126 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____126 in
              [uu____125] in
            uu____121 :: uu____123 in
          uu____118 :: uu____119 in
        FStar_Syntax_Syntax.mk_Tm_app uu____116 uu____117 in
      uu____115 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____133 =
        let uu____134 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero] in
        let uu____135 =
          let uu____136 = FStar_Syntax_Syntax.iarg t_a in
          let uu____137 =
            let uu____139 =
              let uu____140 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____140 in
            let uu____141 =
              let uu____143 =
                let uu____144 = embed_proofstate ps1 in
                FStar_Syntax_Syntax.as_arg uu____144 in
              [uu____143] in
            uu____139 :: uu____141 in
          uu____136 :: uu____137 in
        FStar_Syntax_Syntax.mk_Tm_app uu____134 uu____135 in
      uu____133 None FStar_Range.dummyRange
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res in
  let uu____182 = FStar_Syntax_Util.head_and_args res1 in
  match uu____182 with
  | (hd1,args) ->
      let uu____214 =
        let uu____222 =
          let uu____223 = FStar_Syntax_Util.un_uinst hd1 in
          uu____223.FStar_Syntax_Syntax.n in
        (uu____222, args) in
      (match uu____214 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____240)::(embedded_state,uu____242)::[]) when
           let uu____276 = fstar_tactics_lid' ["Effect"; "Success"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____276 ->
           let uu____277 =
             let uu____280 = unembed_a a in
             let uu____281 = unembed_proofstate ps embedded_state in
             (uu____280, uu____281) in
           FStar_Util.Inl uu____277
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____289)::(embedded_state,uu____291)::[])
           when
           let uu____325 = fstar_tactics_lid' ["Effect"; "Failed"] in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____325 ->
           let uu____326 =
             let uu____329 =
               FStar_Reflection_Basic.unembed_string embedded_string in
             let uu____330 = unembed_proofstate ps embedded_state in
             (uu____329, uu____330) in
           FStar_Util.Inr uu____326
       | uu____335 ->
           let uu____343 =
             let uu____344 = FStar_Syntax_Print.term_to_string res1 in
             FStar_Util.format1 "Not an embedded result: %s" uu____344 in
           failwith uu____343)
>>>>>>> origin/guido_tactics
