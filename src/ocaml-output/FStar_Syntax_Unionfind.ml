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
    let uu____76 = FStar_Unionfind.puf_empty () in
    let uu____78 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____76; univ_graph = uu____78 } in
  let tx_st = { current = init1; rest = [] } in FStar_Util.mk_ref tx_st
let get: Prims.unit -> uf =
  fun uu____87  -> let uu____88 = FStar_ST.read state in uu____88.current
let set: uf -> Prims.unit =
  fun u  ->
    let uu____95 =
      let uu___101_96 = FStar_ST.read state in
      { current = u; rest = (uu___101_96.rest) } in
    FStar_ST.write state uu____95
let reset: Prims.unit -> Prims.unit =
  fun uu____104  ->
    let uu____105 =
      let uu___102_106 = FStar_ST.read state in
      let uu____109 =
        let uu___103_110 =
          let uu____111 = FStar_ST.read state in uu____111.current in
        let uu____114 = FStar_Unionfind.puf_empty () in
        let uu____116 = FStar_Unionfind.puf_empty () in
        { term_graph = uu____114; univ_graph = uu____116 } in
      { current = uu____109; rest = (uu___102_106.rest) } in
    FStar_ST.write state uu____105
let new_transaction: Prims.unit -> tx =
  let tx_ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____126  ->
    let tx =
      FStar_Util.incr tx_ctr;
      (let uu____132 = FStar_ST.read tx_ctr in TX uu____132) in
    (let uu____136 =
       let uu___104_137 = FStar_ST.read state in
       let uu____140 =
         let uu____144 = let uu____147 = get () in (tx, uu____147) in
         let uu____148 =
           let uu____152 = FStar_ST.read state in uu____152.rest in
         uu____144 :: uu____148 in
       { current = (uu___104_137.current); rest = uu____140 } in
     FStar_ST.write state uu____136);
    tx
let commit_or_rollback: Prims.bool -> tx -> Prims.unit =
  fun rb  ->
    fun tx  ->
      let rec aux uu___100_173 =
        match uu___100_173 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____189 =
                  let uu___105_190 = FStar_ST.read state in
                  { current = (uu___105_190.current); rest } in
                FStar_ST.write state uu____189))
            else aux rest in
      let uu____196 = let uu____200 = FStar_ST.read state in uu____200.rest in
      aux uu____196
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____234  -> let uu____235 = get () in uu____235.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___106_241 = get () in
      { term_graph = tg; univ_graph = (uu___106_241.univ_graph) } in
    let uu____242 =
      let uu___107_243 = FStar_ST.read state in
      { current = next; rest = (uu___107_243.rest) } in
    FStar_ST.write state uu____242
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____252 = get_term_graph () in FStar_Unionfind.puf_id uu____252 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____259  ->
    let uu____260 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____260 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____269 = get_term_graph () in FStar_Unionfind.puf_find uu____269 u
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____281 =
        let uu____282 = get_term_graph () in
        FStar_Unionfind.puf_change uu____282 u (Some t) in
      set_term_graph uu____281
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____294 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____294 u v1
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____306 =
        let uu____307 = get_term_graph () in
        FStar_Unionfind.puf_union uu____307 u v1 in
      set_term_graph uu____306
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____314  -> let uu____315 = get () in uu____315.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___108_321 = get () in
      { term_graph = (uu___108_321.term_graph); univ_graph = ug } in
    let uu____322 =
      let uu___109_323 = FStar_ST.read state in
      { current = next; rest = (uu___109_323.rest) } in
    FStar_ST.write state uu____322
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____332 = get_univ_graph () in FStar_Unionfind.puf_id uu____332 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____339  ->
    let uu____340 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____340 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____349 = get_univ_graph () in FStar_Unionfind.puf_find uu____349 u
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____361 =
        let uu____362 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____362 u (Some t) in
      set_univ_graph uu____361
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____374 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____374 u v1
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____386 =
        let uu____387 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____387 u v1 in
      set_univ_graph uu____386