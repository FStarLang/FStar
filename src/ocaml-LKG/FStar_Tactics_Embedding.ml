open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid : Prims.string -> FStar_Ident.lident =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Tactics"] [s])
      FStar_Range.dummyRange
  
let by_tactic_lid : FStar_Ident.lident = fstar_tactics_lid "by_tactic" 
let lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____7 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_All.pipe_right uu____7 FStar_Syntax_Syntax.fv_to_tm
  
let mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____11 = fstar_tactics_lid s  in lid_as_tm uu____11 
let fstar_tactics_term : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "term" 
let fstar_tactics_env : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "env" 
let fstar_tactics_binder : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "binder" 
let fstar_tactics_binders : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "binders" 
let fstar_tactics_goal : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goal" 
let fstar_tactics_goals : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "goals" 
let fstar_tactics_formula : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "formula" 
let fstar_tactics_embed : FStar_Syntax_Syntax.term =
  mk_tactic_lid_as_term "embed" 
let lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____15 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor)
       in
    FStar_Syntax_Syntax.fv_to_tm uu____15
  
let fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____19 = fstar_tactics_lid s  in lid_as_data_tm uu____19 
let fstar_tactics_Failed : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Failed" 
let fstar_tactics_Success : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Success" 
let fstar_tactics_True_ : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "True_" 
let fstar_tactics_False_ : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "False_" 
let fstar_tactics_Eq : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Eq" 
let fstar_tactics_And : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "And" 
let fstar_tactics_Or : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Or" 
let fstar_tactics_Not : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Not" 
let fstar_tactics_Implies : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Implies" 
let fstar_tactics_Iff : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Iff" 
let fstar_tactics_Forall : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Forall" 
let fstar_tactics_Exists : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Exists" 
let fstar_tactics_App : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "App" 
let fstar_tactics_Name : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Name" 
let lid_Mktuple2 : FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
  
let protect_embedded_term :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____28 =
        let uu____29 =
          let uu____30 = FStar_Syntax_Syntax.iarg t  in
          let uu____31 =
            let uu____33 = FStar_Syntax_Syntax.as_arg x  in [uu____33]  in
          uu____30 :: uu____31  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_embed uu____29  in
      uu____28 None x.FStar_Syntax_Syntax.pos
  
let un_protect_embedded_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  let embed_lid = fstar_tactics_lid "embed"  in
  fun t  ->
    let uu____42 = FStar_Syntax_Util.head_and_args t  in
    match uu____42 with
    | (head1,args) ->
        let uu____68 =
          let uu____76 =
            let uu____77 = FStar_Syntax_Subst.compress head1  in
            uu____77.FStar_Syntax_Syntax.n  in
          (uu____76, args)  in
        (match uu____68 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____86::(x,uu____88)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv embed_lid -> x
         | uu____114 ->
             let uu____122 =
               let uu____123 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____123
                in
             failwith uu____122)
  
exception Unembed_failed of Prims.string 
let uu___is_Unembed_failed : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unembed_failed uu____129 -> true
    | uu____130 -> false
  
let __proj__Unembed_failed__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | Unembed_failed uu____137 -> uu____137
  
let embed_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    let uu____141 = FStar_Syntax_Syntax.bv_to_name (Prims.fst b)  in
    protect_embedded_term fstar_tactics_binder uu____141
  
let unembed_binder : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t  in
    let t2 = FStar_Syntax_Util.unascribe t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____148 -> failwith "Not an embedded binder"
  
let embed_pair x embed_a t_a embed_b t_b =
  let uu____192 =
    let uu____193 =
      let uu____194 = lid_as_data_tm lid_Mktuple2  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____194
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
       in
    let uu____195 =
      let uu____196 = FStar_Syntax_Syntax.iarg t_a  in
      let uu____197 =
        let uu____199 = FStar_Syntax_Syntax.iarg t_b  in
        let uu____200 =
          let uu____202 =
            let uu____203 = embed_a (Prims.fst x)  in
            FStar_Syntax_Syntax.as_arg uu____203  in
          let uu____204 =
            let uu____206 =
              let uu____207 = embed_b (Prims.snd x)  in
              FStar_Syntax_Syntax.as_arg uu____207  in
            [uu____206]  in
          uu____202 :: uu____204  in
        uu____199 :: uu____200  in
      uu____196 :: uu____197  in
    FStar_Syntax_Syntax.mk_Tm_app uu____193 uu____195  in
  uu____192 None FStar_Range.dummyRange 
let unembed_pair pair unembed_a unembed_b =
  let pairs = FStar_Syntax_Util.unascribe pair  in
  let uu____244 = FStar_Syntax_Util.head_and_args pair  in
  match uu____244 with
  | (hd1,args) ->
      let uu____272 =
        let uu____280 =
          let uu____281 = FStar_Syntax_Util.un_uinst hd1  in
          uu____281.FStar_Syntax_Syntax.n  in
        (uu____280, args)  in
      (match uu____272 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____292::uu____293::(a,uu____295)::(b,uu____297)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____339 = unembed_a a  in
           let uu____340 = unembed_b b  in (uu____339, uu____340)
       | uu____341 -> failwith "Not an embedded pair")
  
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____375 =
        let uu____376 =
          let uu____377 = lid_as_data_tm FStar_Syntax_Const.none_lid  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____377
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____378 =
          let uu____379 = FStar_Syntax_Syntax.iarg typ  in [uu____379]  in
        FStar_Syntax_Syntax.mk_Tm_app uu____376 uu____378  in
      uu____375 None FStar_Range.dummyRange
  | Some a ->
      let uu____385 =
        let uu____386 =
          let uu____387 = lid_as_data_tm FStar_Syntax_Const.some_lid  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____387
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____388 =
          let uu____389 = FStar_Syntax_Syntax.iarg typ  in
          let uu____390 =
            let uu____392 =
              let uu____393 = embed_a a  in
              FStar_Syntax_Syntax.as_arg uu____393  in
            [uu____392]  in
          uu____389 :: uu____390  in
        FStar_Syntax_Syntax.mk_Tm_app uu____386 uu____388  in
      uu____385 None FStar_Range.dummyRange
  
let unembed_option unembed_a o =
  let uu____416 = FStar_Syntax_Util.head_and_args o  in
  match uu____416 with
  | (hd1,args) ->
      let uu____443 =
        let uu____451 =
          let uu____452 = FStar_Syntax_Util.un_uinst hd1  in
          uu____452.FStar_Syntax_Syntax.n  in
        (uu____451, args)  in
      (match uu____443 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____462) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____474::(a,uu____476)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____502 = unembed_a a  in Some uu____502
       | uu____503 -> failwith "Not an embedded option")
  
let rec embed_list l embed_a t_a =
  match l with
  | [] ->
      let uu____536 =
        let uu____537 =
          let uu____538 = lid_as_data_tm FStar_Syntax_Const.nil_lid  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____538
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____539 =
          let uu____540 = FStar_Syntax_Syntax.iarg t_a  in [uu____540]  in
        FStar_Syntax_Syntax.mk_Tm_app uu____537 uu____539  in
      uu____536 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____548 =
        let uu____549 =
          let uu____550 = lid_as_data_tm FStar_Syntax_Const.cons_lid  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____550
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____551 =
          let uu____552 = FStar_Syntax_Syntax.iarg t_a  in
          let uu____553 =
            let uu____555 =
              let uu____556 = embed_a hd1  in
              FStar_Syntax_Syntax.as_arg uu____556  in
            let uu____557 =
              let uu____559 =
                let uu____560 = embed_list tl1 embed_a t_a  in
                FStar_Syntax_Syntax.as_arg uu____560  in
              [uu____559]  in
            uu____555 :: uu____557  in
          uu____552 :: uu____553  in
        FStar_Syntax_Syntax.mk_Tm_app uu____549 uu____551  in
      uu____548 None FStar_Range.dummyRange
  
let rec unembed_list l unembed_a =
  let l1 = FStar_Syntax_Util.unascribe l  in
  let uu____584 = FStar_Syntax_Util.head_and_args l1  in
  match uu____584 with
  | (hd1,args) ->
      let uu____611 =
        let uu____619 =
          let uu____620 = FStar_Syntax_Util.un_uinst hd1  in
          uu____620.FStar_Syntax_Syntax.n  in
        (uu____619, args)  in
      (match uu____611 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____630) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____644)::(tl1,uu____646)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____680 = unembed_a hd2  in
           let uu____681 = unembed_list tl1 unembed_a  in uu____680 ::
             uu____681
       | uu____683 ->
           let uu____691 =
             let uu____692 = FStar_Syntax_Print.term_to_string l1  in
             FStar_Util.format1 "Not an embedded list: %s" uu____692  in
           failwith uu____691)
  
let embed_binders :
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list l embed_binder fstar_tactics_binder 
let unembed_binders :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list t unembed_binder 
let embed_env :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    let uu____706 =
      let uu____707 = FStar_TypeChecker_Env.all_binders env  in
      embed_list uu____707 embed_binder fstar_tactics_binder  in
    protect_embedded_term fstar_tactics_env uu____706
  
let unembed_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun protected_embedded_env  ->
      let embedded_env = un_protect_embedded_term protected_embedded_env  in
      let binders = unembed_list embedded_env unembed_binder  in
      (let uu____723 = FStar_Syntax_Print.binders_to_string ", " binders  in
       FStar_Util.print1 "Unembedding environment: %s\n" uu____723);
      FStar_List.fold_left
        (fun env1  ->
           fun b  ->
             let uu____730 =
               FStar_TypeChecker_Env.try_lookup_bv env1 (Prims.fst b)  in
             match uu____730 with
             | None  -> FStar_TypeChecker_Env.push_binders env1 [b]
             | uu____740 -> env1) env binders
  
let embed_term :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term fstar_tactics_term t 
let unembed_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t 
let embed_goal : FStar_Tactics_Basic.goal -> FStar_Syntax_Syntax.term =
  fun g  ->
    embed_pair
      ((g.FStar_Tactics_Basic.context), (g.FStar_Tactics_Basic.goal_ty))
      embed_env fstar_tactics_env embed_term fstar_tactics_term
  
let unembed_goal :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal
  =
  fun env  ->
    fun t  ->
      let uu____759 = unembed_pair t (unembed_env env) unembed_term  in
      match uu____759 with
      | (env1,goal_ty) ->
          {
            FStar_Tactics_Basic.context = env1;
            FStar_Tactics_Basic.witness = None;
            FStar_Tactics_Basic.goal_ty = goal_ty
          }
  
let embed_goals :
  FStar_Tactics_Basic.goal Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list l embed_goal fstar_tactics_goal 
let unembed_goals :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.goal Prims.list
  = fun env  -> fun egs  -> unembed_list egs (unembed_goal env) 
type state =
  (FStar_Tactics_Basic.goal Prims.list * FStar_Tactics_Basic.goal Prims.list)
let embed_state : state -> FStar_Syntax_Syntax.term =
  fun s  ->
    embed_pair s embed_goals fstar_tactics_goals embed_goals
      fstar_tactics_goals
  
let unembed_state :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Tactics_Basic.goal Prims.list * FStar_Tactics_Basic.goal
        Prims.list)
  =
  fun env  ->
    fun s  ->
      let s1 = FStar_Syntax_Util.unascribe s  in
      unembed_pair s1 (unembed_goals env) (unembed_goals env)
  
let embed_unit : Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit 
let unembed_unit : FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____800  -> () 
let embed_bool : Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
  
let unembed_bool : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____808 =
      let uu____809 = FStar_Syntax_Subst.compress t  in
      uu____809.FStar_Syntax_Syntax.n  in
    match uu____808 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____813 -> failwith "Not an embedded bool"
  
let embed_string :
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s  in
    (FStar_Syntax_Syntax.mk
       (FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))) None
      FStar_Range.dummyRange
  
let unembed_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____833)) -> FStar_Util.string_of_unicode bytes
    | uu____836 -> failwith "Not an embedded string"
  
let embed_result res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps) ->
      let uu____863 =
        let uu____864 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____865 =
          let uu____866 = FStar_Syntax_Syntax.iarg t_a  in
          let uu____867 =
            let uu____869 =
              let uu____870 = embed_string msg  in
              FStar_Syntax_Syntax.as_arg uu____870  in
            let uu____871 =
              let uu____873 =
                let uu____874 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals))
                   in
                FStar_Syntax_Syntax.as_arg uu____874  in
              [uu____873]  in
            uu____869 :: uu____871  in
          uu____866 :: uu____867  in
        FStar_Syntax_Syntax.mk_Tm_app uu____864 uu____865  in
      uu____863 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps) ->
      let uu____883 =
        let uu____884 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____885 =
          let uu____886 = FStar_Syntax_Syntax.iarg t_a  in
          let uu____887 =
            let uu____889 =
              let uu____890 = embed_a a  in
              FStar_Syntax_Syntax.as_arg uu____890  in
            let uu____891 =
              let uu____893 =
                let uu____894 =
                  embed_state
                    ((ps.FStar_Tactics_Basic.goals),
                      (ps.FStar_Tactics_Basic.smt_goals))
                   in
                FStar_Syntax_Syntax.as_arg uu____894  in
              [uu____893]  in
            uu____889 :: uu____891  in
          uu____886 :: uu____887  in
        FStar_Syntax_Syntax.mk_Tm_app uu____884 uu____885  in
      uu____883 None FStar_Range.dummyRange
  
let unembed_result env res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res  in
  let uu____930 = FStar_Syntax_Util.head_and_args res1  in
  match uu____930 with
  | (hd1,args) ->
      let uu____962 =
        let uu____970 =
          let uu____971 = FStar_Syntax_Util.un_uinst hd1  in
          uu____971.FStar_Syntax_Syntax.n  in
        (uu____970, args)  in
      (match uu____962 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____988)::(embedded_state,uu____990)::[]) when
           let uu____1024 = fstar_tactics_lid "Success"  in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1024 ->
           let uu____1025 =
             let uu____1028 = unembed_a a  in
             let uu____1029 = unembed_state env embedded_state  in
             (uu____1028, uu____1029)  in
           FStar_Util.Inl uu____1025
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____1037)::(embedded_state,uu____1039)::[])
           when
           let uu____1073 = fstar_tactics_lid "Failed"  in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____1073 ->
           let uu____1074 =
             let uu____1077 = unembed_string embedded_string  in
             let uu____1078 = unembed_state env embedded_state  in
             (uu____1077, uu____1078)  in
           FStar_Util.Inr uu____1074
       | uu____1083 ->
           let uu____1091 =
             let uu____1092 = FStar_Syntax_Print.term_to_string res1  in
             FStar_Util.format1 "Not an embedded result: %s" uu____1092  in
           failwith uu____1091)
  
type formula =
  | Connective of FStar_Syntax_Util.connective 
  | App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list) 
  | Name of FStar_Syntax_Syntax.bv 
let uu___is_Connective : formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Connective _0 -> true | uu____1115 -> false
  
let __proj__Connective__item___0 : formula -> FStar_Syntax_Util.connective =
  fun projectee  -> match projectee with | Connective _0 -> _0 
let uu___is_App : formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1130 -> false
  
let __proj__App__item___0 :
  formula -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list)
  = fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Name : formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____1151 -> false
  
let __proj__Name__item___0 : formula -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Name _0 -> _0 
let embed_formula : formula -> FStar_Syntax_Syntax.term =
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
                        (let uu____1178 =
                           let uu____1179 = FStar_Ident.string_of_lid l  in
                           Prims.strcat "Unrecognized connective" uu____1179
                            in
                         failwith uu____1178)
         in
      match args with
      | [] -> hd1
      | uu____1184 ->
          let uu____1185 =
            let uu____1186 =
              FStar_List.map
                (fun uu____1189  ->
                   match uu____1189 with
                   | (x,uu____1193) ->
                       let uu____1194 = embed_term x  in
                       FStar_Syntax_Syntax.as_arg uu____1194) args
               in
            FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1186  in
          uu____1185 None FStar_Range.dummyRange
       in
    match f with
    | Connective (FStar_Syntax_Util.QAll (binders,qpats,typ)) ->
        let uu____1202 =
          let uu____1203 =
            let uu____1204 =
              let uu____1205 = embed_binders binders  in
              FStar_Syntax_Syntax.as_arg uu____1205  in
            let uu____1206 =
              let uu____1208 =
                let uu____1209 = embed_term typ  in
                FStar_Syntax_Syntax.as_arg uu____1209  in
              [uu____1208]  in
            uu____1204 :: uu____1206  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Forall uu____1203  in
        uu____1202 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.QEx (binders,qpats,typ)) ->
        let uu____1217 =
          let uu____1218 =
            let uu____1219 =
              let uu____1220 = embed_binders binders  in
              FStar_Syntax_Syntax.as_arg uu____1220  in
            let uu____1221 =
              let uu____1223 =
                let uu____1224 = embed_term typ  in
                FStar_Syntax_Syntax.as_arg uu____1224  in
              [uu____1223]  in
            uu____1219 :: uu____1221  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Exists uu____1218  in
        uu____1217 None FStar_Range.dummyRange
    | Connective (FStar_Syntax_Util.BaseConn (lid,args)) ->
        encode_app lid args
    | App (t,ts) ->
        let uu____1235 =
          let uu____1236 =
            let uu____1237 =
              let uu____1238 = embed_term t  in
              FStar_Syntax_Syntax.as_arg uu____1238  in
            let uu____1239 =
              let uu____1241 =
                let uu____1242 = embed_list ts embed_term fstar_tactics_term
                   in
                FStar_Syntax_Syntax.as_arg uu____1242  in
              [uu____1241]  in
            uu____1237 :: uu____1239  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_App uu____1236  in
        uu____1235 None FStar_Range.dummyRange
    | Name bv ->
        let uu____1248 =
          let uu____1249 =
            let uu____1250 =
              let uu____1251 =
                let uu____1252 = FStar_Syntax_Syntax.mk_binder bv  in
                embed_binder uu____1252  in
              FStar_Syntax_Syntax.as_arg uu____1251  in
            [uu____1250]  in
          FStar_Syntax_Syntax.mk_Tm_app fstar_tactics_Name uu____1249  in
        uu____1248 None FStar_Range.dummyRange
  
let term_as_formula : FStar_Syntax_Syntax.term -> formula Prims.option =
  fun t  ->
    let uu____1262 = FStar_Syntax_Util.destruct_typ_as_formula t  in
    match uu____1262 with
    | Some c -> Some (Connective c)
    | uu____1266 ->
        let uu____1268 =
          let uu____1269 = FStar_Syntax_Subst.compress t  in
          uu____1269.FStar_Syntax_Syntax.n  in
        (match uu____1268 with
         | FStar_Syntax_Syntax.Tm_app uu____1273 ->
             let uu____1283 = FStar_Syntax_Util.head_and_args t  in
             (match uu____1283 with
              | (hd1,args) ->
                  let uu____1310 =
                    let uu____1311 =
                      let uu____1315 = FStar_List.map Prims.fst args  in
                      (hd1, uu____1315)  in
                    App uu____1311  in
                  Some uu____1310)
         | FStar_Syntax_Syntax.Tm_name bv -> Some (Name bv)
         | uu____1333 -> None)
  