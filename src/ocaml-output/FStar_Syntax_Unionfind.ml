open Prims
type tgraph = FStar_Syntax_Syntax.term option FStar_Unionfind.puf
type ugraph = FStar_Syntax_Syntax.universe option FStar_Unionfind.puf
type uf = {
  term_graph: tgraph;
  univ_graph: ugraph;}
let __proj__Mkuf__item__term_graph: uf -> tgraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;_}
        -> __fname__term_graph
let __proj__Mkuf__item__univ_graph: uf -> ugraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;_}
        -> __fname__univ_graph
type tx =
  | TX of Prims.int
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> Prims.int =
  fun projectee  -> match projectee with | TX _0 -> _0
type transactional_state = {
  current: uf;
  rest: (tx* uf) Prims.list;}
let __proj__Mktransactional_state__item__current: transactional_state -> uf =
  fun projectee  ->
    match projectee with
    | { current = __fname__current; rest = __fname__rest;_} ->
        __fname__current
let __proj__Mktransactional_state__item__rest:
  transactional_state -> (tx* uf) Prims.list =
  fun projectee  ->
    match projectee with
    | { current = __fname__current; rest = __fname__rest;_} -> __fname__rest
let state: transactional_state FStar_ST.ref =
  let init1 =
    let uu____70 = FStar_Unionfind.puf_empty () in
    let uu____72 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____70; univ_graph = uu____72 } in
  let tx_st = { current = init1; rest = [] } in FStar_Util.mk_ref tx_st
let get: Prims.unit -> uf =
  fun uu____80  -> let uu____81 = FStar_ST.read state in uu____81.current
let set: uf -> Prims.unit =
  fun u  ->
    let uu____87 =
      let uu___101_88 = FStar_ST.read state in
      { current = u; rest = (uu___101_88.rest) } in
    FStar_ST.write state uu____87
let reset: Prims.unit -> Prims.unit =
  fun uu____95  ->
    let uu____96 =
      let uu___102_97 = FStar_ST.read state in
      let uu____100 =
        let uu___103_101 =
          let uu____102 = FStar_ST.read state in uu____102.current in
        let uu____105 = FStar_Unionfind.puf_empty () in
        let uu____107 = FStar_Unionfind.puf_empty () in
        { term_graph = uu____105; univ_graph = uu____107 } in
      { current = uu____100; rest = (uu___102_97.rest) } in
    FStar_ST.write state uu____96
let new_transaction: Prims.unit -> tx =
  let tx_ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____116  ->
    let tx =
      FStar_Util.incr tx_ctr;
      (let uu____122 = FStar_ST.read tx_ctr in TX uu____122) in
    (let uu____126 =
       let uu___104_127 = FStar_ST.read state in
       let uu____130 =
         let uu____134 = let uu____137 = get () in (tx, uu____137) in
         let uu____138 =
           let uu____142 = FStar_ST.read state in uu____142.rest in
         uu____134 :: uu____138 in
       { current = (uu___104_127.current); rest = uu____130 } in
     FStar_ST.write state uu____126);
    tx
let commit_or_rollback: Prims.bool -> tx -> Prims.unit =
  fun rb  ->
    fun tx  ->
      let rec aux uu___100_161 =
        match uu___100_161 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____177 =
                  let uu___105_178 = FStar_ST.read state in
                  { current = (uu___105_178.current); rest } in
                FStar_ST.write state uu____177))
            else aux rest in
      let uu____184 = let uu____188 = FStar_ST.read state in uu____188.rest in
      aux uu____184
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____216  -> let uu____217 = get () in uu____217.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___106_222 = get () in
      { term_graph = tg; univ_graph = (uu___106_222.univ_graph) } in
    let uu____223 =
      let uu___107_224 = FStar_ST.read state in
      { current = next; rest = (uu___107_224.rest) } in
    FStar_ST.write state uu____223
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____232 = get_term_graph () in FStar_Unionfind.puf_id uu____232 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____238  ->
    let uu____239 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____239 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____247 = get_term_graph () in FStar_Unionfind.puf_find uu____247 u
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____257 =
        let uu____258 = get_term_graph () in
        FStar_Unionfind.puf_change uu____258 u (Some t) in
      set_term_graph uu____257
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____268 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____268 u v1
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____278 =
        let uu____279 = get_term_graph () in
        FStar_Unionfind.puf_union uu____279 u v1 in
      set_term_graph uu____278
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____285  -> let uu____286 = get () in uu____286.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___108_291 = get () in
      { term_graph = (uu___108_291.term_graph); univ_graph = ug } in
    let uu____292 =
      let uu___109_293 = FStar_ST.read state in
      { current = next; rest = (uu___109_293.rest) } in
    FStar_ST.write state uu____292
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____301 = get_univ_graph () in FStar_Unionfind.puf_id uu____301 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____307  ->
    let uu____308 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____308 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____316 = get_univ_graph () in FStar_Unionfind.puf_find uu____316 u
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____326 =
        let uu____327 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____327 u (Some t) in
      set_univ_graph uu____326
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____337 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____337 u v1
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____347 =
        let uu____348 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____348 u v1 in
      set_univ_graph uu____347