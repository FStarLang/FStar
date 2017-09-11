open Prims
type 'Aa __result =
  | Success of 'Aa* FStar_Tactics_Types.proofstate
  | Failed of Prims.string* FStar_Tactics_Types.proofstate
let uu___is_Success: 'Aa . 'Aa __result -> Prims.bool =
  fun projectee  ->
    match projectee with | Success (_0,_1) -> true | uu____44 -> false
let __proj__Success__item___0: 'Aa . 'Aa __result -> 'Aa =
  fun projectee  -> match projectee with | Success (_0,_1) -> _0
let __proj__Success__item___1:
  'Aa . 'Aa __result -> FStar_Tactics_Types.proofstate =
  fun projectee  -> match projectee with | Success (_0,_1) -> _1
let uu___is_Failed: 'Aa . 'Aa __result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed (_0,_1) -> true | uu____113 -> false
let __proj__Failed__item___0: 'Aa . 'Aa __result -> Prims.string =
  fun projectee  -> match projectee with | Failed (_0,_1) -> _0
let __proj__Failed__item___1:
  'Aa . 'Aa __result -> FStar_Tactics_Types.proofstate =
  fun projectee  -> match projectee with | Failed (_0,_1) -> _1
type 'Aa __tac = FStar_Tactics_Types.proofstate -> 'Aa __result
let __ret: 'Aa . 'Aa -> 'Aa __tac = fun x  -> fun s  -> Success (x, s)
let __bind: 'Aa 'Ab . 'Aa __tac -> ('Aa -> 'Ab __tac) -> 'Ab __tac =
  fun t1  ->
    fun t2  ->
      fun p  ->
        match t1 p with
        | Success (a,q) -> t2 a q
        | Failed (msg,q) -> Failed (msg, q)
let __get: Prims.unit -> FStar_Tactics_Types.proofstate __tac =
  fun uu____264  -> fun s0  -> Success (s0, s0)
type 'Aa __tac_wp = FStar_Tactics_Types.proofstate -> Prims.unit -> Obj.t
type ('Aa,'Ab,'Awp,'Af,'Aps,'Apost) g_bind = 'Awp
type ('Aa,'Awp,'Aps,'Apost) g_compact = Prims.unit
type ('Ar,'Aa,'Ab,'Awp,'Af,'Auu____411,'Auu____412) __TAC_eff_override_bind_wp =
  Prims.unit
type ('Aa,'Awp,'As,'Ap') _dm4f_TAC_lift_from_pure = 'Awp
type ('Aa,'Ax,'As,'Ap') _dm4f_TAC_return_wp = 'Ap'
let _dm4f_TAC_return_elab:
  'Aa . 'Aa -> FStar_Tactics_Types.proofstate -> 'Aa __result =
  fun x  -> fun s  -> Success (x, s)
let _dm4f_TAC_bind_elab:
  'Aa 'Ab 'At1__w .
    (FStar_Tactics_Types.proofstate -> 'Aa __result) ->
      Prims.unit ->
        ('Aa -> FStar_Tactics_Types.proofstate -> 'Ab __result) ->
          FStar_Tactics_Types.proofstate -> 'Ab __result
  =
  fun t1  ->
    fun t2__w  ->
      fun t2  ->
        fun p  ->
          match t1 p with
          | Success (a,q) -> t2 a q
          | Failed (msg,q) -> Failed (msg, q)
let _dm4f_TAC___proj__TAC__item____get_elab:
  Prims.unit ->
    FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.proofstate __result
  = fun uu____637  -> fun s0  -> Success (s0, s0)
type _dm4f_TAC___proj__TAC__item____get_complete_type =
  Prims.unit ->
    FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.proofstate __result
type ('Aa,'Awp_a) _dm4f_TAC_repr =
  FStar_Tactics_Types.proofstate -> 'Aa __result
type _dm4f_TAC_pre = FStar_Tactics_Types.proofstate -> Obj.t
type 'Aa _dm4f_TAC_post = 'Aa __result -> Obj.t
type 'Aa _dm4f_TAC_wp = FStar_Tactics_Types.proofstate -> Prims.unit -> Obj.t
type ('Aa,'At) _dm4f_TAC_ctx =
  FStar_Tactics_Types.proofstate -> Prims.unit -> 'At
type ('Aa,'At) _dm4f_TAC_gctx =
  FStar_Tactics_Types.proofstate -> Prims.unit -> 'At
let _dm4f_TAC_pure:
  'Aa 'At . 'At -> FStar_Tactics_Types.proofstate -> Prims.unit -> 'At =
  fun x  -> fun uu____745  -> fun uu____746  -> x
let _dm4f_TAC_app:
  'Aa 'At1 'At2 .
    (FStar_Tactics_Types.proofstate -> Prims.unit -> 'At1 -> 'At2) ->
      (FStar_Tactics_Types.proofstate -> Prims.unit -> 'At1) ->
        FStar_Tactics_Types.proofstate -> Prims.unit -> 'At2
  = fun l  -> fun r  -> fun uu____820  -> fun uu____821  -> Obj.magic ()
let _dm4f_TAC_lift1:
  'Aa 'At1 'At2 .
    ('At1 -> 'At2) ->
      (FStar_Tactics_Types.proofstate -> Prims.unit -> 'At1) ->
        FStar_Tactics_Types.proofstate -> Prims.unit -> 'At2
  = fun f1  -> fun a1  -> fun uu____891  -> fun uu____892  -> Obj.magic ()
let _dm4f_TAC_lift2:
  'Aa 'At1 'At2 'At3 .
    ('At1 -> 'At2 -> 'At3) ->
      (FStar_Tactics_Types.proofstate -> Prims.unit -> 'At1) ->
        (FStar_Tactics_Types.proofstate -> Prims.unit -> 'At2) ->
          FStar_Tactics_Types.proofstate -> Prims.unit -> 'At3
  =
  fun f1  ->
    fun a1  -> fun a2  -> fun uu____982  -> fun uu____983  -> Obj.magic ()
let _dm4f_TAC_push:
  'Aa 'At1 'At2 .
    ('At1 -> FStar_Tactics_Types.proofstate -> Prims.unit -> 'At2) ->
      FStar_Tactics_Types.proofstate -> Prims.unit -> 'At1 -> 'At2
  = fun f1  -> fun uu____1058  -> fun uu____1059  -> fun e1  -> Obj.magic ()
type ('Aa,'Ac,'Auu____1091,'Auu____1092,'Auu____1093,'Auu____1094) _dm4f_TAC_wp_if_then_else =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____1129,'Auu____1130) _dm4f_TAC_wp_assert =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____1155,'Auu____1156) _dm4f_TAC_wp_assume =
  Prims.unit
type ('Aa,'Ab,'Af,'Auu____1182,'Auu____1183) _dm4f_TAC_wp_close = Prims.unit
type ('Aa,'Awp1,'Awp2) _dm4f_TAC_stronger = Prims.unit
type ('Aa,'Awp,'Auu____1253,'Auu____1254) _dm4f_TAC_wp_ite = Prims.unit
type ('Aa,'Auu____1299,'Auu____1300) _dm4f_TAC_null_wp = Prims.unit
type ('Aa,'Awp) _dm4f_TAC_wp_trivial = Prims.unit
let __proj__TAC__item__return = _dm4f_TAC_return_elab
let __proj__TAC__item__bind = _dm4f_TAC_bind_elab
let __proj__TAC__item____get uu____1379 s0 = Success (s0, s0)
type 'Aa tactic = Prims.unit -> ('Aa,Prims.unit) _dm4f_TAC_repr
let return: 'Aa . 'Aa -> 'Aa tactic =
  fun x  -> fun uu____1435  -> fun s  -> Success (x, s)
let bind: 'Aa 'Ab . 'Aa tactic -> ('Aa -> 'Ab tactic) -> 'Ab tactic =
  fun t  ->
    fun f1  ->
      fun uu____1483  ->
        fun p  ->
          match (t ()) p with
          | Success (a,q) -> (f1 a ()) q
          | Failed (msg,q) -> Failed (msg, q)
let get:
  Prims.unit ->
    (FStar_Tactics_Types.proofstate,(FStar_Tactics_Types.proofstate __result,
                                      Obj.t) Prims.l_Forall)
      _dm4f_TAC_repr
  =
  fun a648  ->
    (Obj.magic (fun uu____1560  -> __proj__TAC__item____get ())) a648
let reify_tactic: 'a . 'a tactic -> 'a __tac = fun t  -> fun s  -> (t ()) s
type ('a,'At,'Ap) __by_tactic = 'Ap
type ('a,'At,'Ap) by_tactic = (Obj.t,Prims.unit,'Ap) __by_tactic
let synth_by_tactic: 'At 'Aa . 'Aa tactic -> 'At =
  fun a649  ->
    (Obj.magic
       (fun uu____1652  -> failwith "Not yet implemented:synth_by_tactic"))
      a649
let assert_by_tactic: Prims.unit -> Prims.unit tactic -> Prims.unit =
  fun p  -> fun t  -> ()
let by_tactic_seman: 'Aa . 'Aa tactic -> Prims.unit -> Prims.unit =
  fun tau  -> fun phi  -> ()
