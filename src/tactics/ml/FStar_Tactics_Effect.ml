open Prims
type goal =
  ((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
    FStar_Reflection_Syntax.term)
type goals = goal Prims.list
type state = (goals* goals)
type 'Aa __result =
  | Success of 'Aa* state
  | Failed of Prims.string* state
let uu___is_Success projectee =
  match projectee with | Success (_0,_1) -> true | uu____47 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success (_0,_1) -> _0
let __proj__Success__item___1 projectee =
  match projectee with | Success (_0,_1) -> _1
let uu___is_Failed projectee =
  match projectee with | Failed (_0,_1) -> true | uu____109 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed (_0,_1) -> _0
let __proj__Failed__item___1 projectee =
  match projectee with | Failed (_0,_1) -> _1
type 'Aa __tac = state -> 'Aa __result
let __ret x s = Success (x, s)
let __bind t1 t2 p =
  match t1 p with
  | Success (a,q) -> t2 a q
  | Failed (msg,q) -> Failed (msg, q)
let __get: Prims.unit -> state -> state __result =
  fun uu____247  -> fun s0  -> Success (s0, s0)
type 'Aa __tac_wp = state -> Prims.unit -> Obj.t
type ('Aa,'Ab,'Awp,'Af,'Aps,'Apost) g_bind = 'Awp
type ('Aa,'Awp) g_compact = Prims.unit
type ('Ar,'Aa,'Ab,'Awp,'Af) __TAC_eff_override_bind_wp = Prims.unit
type ('Aa,'Awp,'As,'Ap') _dm4f_TAC_lift_from_pure = 'Awp
type ('Aa,'Ax,'As,'Ap') _dm4f_TAC_return_wp = 'Ap'
let _dm4f_TAC_return_elab x s = Success (x, s)
let _dm4f_TAC_bind_elab t1 t2__w t2 p =
  match t1 p with
  | Success (a,q) -> t2 a q
  | Failed (msg,q) -> Failed (msg, q)
let _dm4f_TAC___proj__TAC__item____get_elab:
  Prims.unit ->
    (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
      FStar_Reflection_Syntax.term) Prims.list*
      ((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
      FStar_Reflection_Syntax.term) Prims.list) ->
      (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
        FStar_Reflection_Syntax.term) Prims.list*
        ((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
        FStar_Reflection_Syntax.term) Prims.list) __result
  = fun uu____666  -> fun s0  -> Success (s0, s0)
type _dm4f_TAC___proj__TAC__item____get_complete_type =
  Prims.unit ->
    (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
      FStar_Reflection_Syntax.term) Prims.list*
      ((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
      FStar_Reflection_Syntax.term) Prims.list) ->
      (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
        FStar_Reflection_Syntax.term) Prims.list*
        ((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
        FStar_Reflection_Syntax.term) Prims.list) __result
type ('Aa,'Awp_a) _dm4f_TAC_repr =
  (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
    FStar_Reflection_Syntax.term) Prims.list* ((FStar_Reflection_Syntax.env*
    FStar_Reflection_Syntax.term)* FStar_Reflection_Syntax.term) Prims.list)
    -> 'Aa __result
type _dm4f_TAC_pre =
  (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
    FStar_Reflection_Syntax.term) Prims.list* ((FStar_Reflection_Syntax.env*
    FStar_Reflection_Syntax.term)* FStar_Reflection_Syntax.term) Prims.list)
    -> Obj.t
type 'Aa _dm4f_TAC_post = 'Aa __result -> Obj.t
type 'Aa _dm4f_TAC_wp =
  (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
    FStar_Reflection_Syntax.term) Prims.list* ((FStar_Reflection_Syntax.env*
    FStar_Reflection_Syntax.term)* FStar_Reflection_Syntax.term) Prims.list)
    -> Prims.unit -> Obj.t
type ('Aa,'At) _dm4f_TAC_ctx =
  (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
    FStar_Reflection_Syntax.term) Prims.list* ((FStar_Reflection_Syntax.env*
    FStar_Reflection_Syntax.term)* FStar_Reflection_Syntax.term) Prims.list)
    -> Prims.unit -> 'At
type ('Aa,'At) _dm4f_TAC_gctx =
  (((FStar_Reflection_Syntax.env* FStar_Reflection_Syntax.term)*
    FStar_Reflection_Syntax.term) Prims.list* ((FStar_Reflection_Syntax.env*
    FStar_Reflection_Syntax.term)* FStar_Reflection_Syntax.term) Prims.list)
    -> Prims.unit -> 'At
let _dm4f_TAC_pure x uu____923 uu____924 = x
let _dm4f_TAC_app l r uu____1042 uu____1043 = Obj.magic ()
let _dm4f_TAC_lift1 f a1 uu____1173 uu____1174 = Obj.magic ()
let _dm4f_TAC_lift2 f a1 a2 uu____1324 uu____1325 = Obj.magic ()
let _dm4f_TAC_push f uu____1455 uu____1456 e1 = Obj.magic ()
type ('Aa,'Ac,'Auu____1501,'Auu____1502,'Auu____1503,'Auu____1504) _dm4f_TAC_wp_if_then_else =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____1525,'Auu____1526) _dm4f_TAC_wp_assert =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____1542,'Auu____1543) _dm4f_TAC_wp_assume =
  Prims.unit
type ('Aa,'Ab,'Af,'Auu____1560,'Auu____1561) _dm4f_TAC_wp_close = Prims.unit
type ('Aa,'Awp1,'Awp2) _dm4f_TAC_stronger = Prims.unit
type ('Aa,'Awp,'Auu____1626,'Auu____1627) _dm4f_TAC_wp_ite = Prims.unit
type ('Aa,'Auu____1654,'Auu____1655) _dm4f_TAC_null_wp = Prims.unit
type ('Aa,'Awp) _dm4f_TAC_wp_trivial = Prims.unit
let __proj__TAC__item__return = _dm4f_TAC_return_elab
let __proj__TAC__item__bind = _dm4f_TAC_bind_elab
let __proj__TAC__item____get uu____1748 s0 = Success (s0, s0)
type 'Aa tactic = Prims.unit -> ('Aa,Prims.unit) _dm4f_TAC_repr
let return x uu____1860 s = Success (x, s)
let bind t f uu____1916 p =
  match (t ()) p with
  | Success (a,q) -> (f a ()) q
  | Failed (msg,q) -> Failed (msg, q)
let get:
  Prims.unit -> (state,(state __result,Obj.t) Prims.l_Forall) _dm4f_TAC_repr
  = Obj.magic (fun uu____2013  -> __proj__TAC__item____get ())
let reify_tactic t s = (t ()) s
type ('a,'At,'Ap) __by_tactic = 'Ap
type ('a,'At,'Ap) by_tactic = (Obj.t,Prims.unit,'Ap) __by_tactic
let synth_by_tactic =
  Obj.magic
    (fun uu____2092  -> failwith "Not yet implemented:synth_by_tactic")
let assert_by_tactic: Prims.unit tactic -> Prims.unit -> Prims.unit =
  fun t  -> fun p  -> ()
let by_tactic_seman tau phi = ()