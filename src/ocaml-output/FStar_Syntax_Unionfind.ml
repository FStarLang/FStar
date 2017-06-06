open Prims
type tgraph = FStar_Syntax_Syntax.term option FStar_Unionfind.puf
type ugraph = FStar_Syntax_Syntax.universe option FStar_Unionfind.puf
type uf = {
  term_graph: tgraph;
  univ_graph: ugraph;}
type tx =
  | TX of Prims.int
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> Prims.int =
  fun projectee  -> match projectee with | TX _0 -> _0
type transactional_state = {
  current: uf;
  rest: (tx* uf) Prims.list;}
let state: transactional_state FStar_ST.ref =
  let init1 =
    let uu____60 = FStar_Unionfind.puf_empty () in
    let uu____62 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____60; univ_graph = uu____62 } in
  let tx_st = { current = init1; rest = [] } in FStar_Util.mk_ref tx_st
let get: Prims.unit -> uf =
  fun uu____70  -> let uu____71 = FStar_ST.read state in uu____71.current
let set: uf -> Prims.unit =
  fun u  ->
    let uu____77 =
      let uu___100_78 = FStar_ST.read state in
      { current = u; rest = (uu___100_78.rest) } in
    FStar_ST.write state uu____77
let reset: Prims.unit -> Prims.unit =
  fun uu____85  ->
    let uu____86 =
      let uu___101_87 = FStar_ST.read state in
      let uu____90 =
        let uu___102_91 =
          let uu____92 = FStar_ST.read state in uu____92.current in
        let uu____95 = FStar_Unionfind.puf_empty () in
        let uu____97 = FStar_Unionfind.puf_empty () in
        { term_graph = uu____95; univ_graph = uu____97 } in
      { current = uu____90; rest = (uu___101_87.rest) } in
    FStar_ST.write state uu____86
let new_transaction: Prims.unit -> tx =
  let tx_ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____106  ->
    let tx =
      FStar_Util.incr tx_ctr;
      (let uu____112 = FStar_ST.read tx_ctr in TX uu____112) in
    (let uu____116 =
       let uu___103_117 = FStar_ST.read state in
       let uu____120 =
         let uu____124 = let uu____127 = get () in (tx, uu____127) in
         let uu____128 =
           let uu____132 = FStar_ST.read state in uu____132.rest in
         uu____124 :: uu____128 in
       { current = (uu___103_117.current); rest = uu____120 } in
     FStar_ST.write state uu____116);
    tx
let commit_or_rollback: Prims.bool -> tx -> Prims.unit =
  fun rb  ->
    fun tx  ->
      let rec aux uu___99_151 =
        match uu___99_151 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____167 =
                  let uu___104_168 = FStar_ST.read state in
                  { current = (uu___104_168.current); rest } in
                FStar_ST.write state uu____167))
            else aux rest in
      let uu____174 = let uu____178 = FStar_ST.read state in uu____178.rest in
      aux uu____174
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____206  -> let uu____207 = get () in uu____207.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___105_212 = get () in
      { term_graph = tg; univ_graph = (uu___105_212.univ_graph) } in
    let uu____213 =
      let uu___106_214 = FStar_ST.read state in
      { current = next; rest = (uu___106_214.rest) } in
    FStar_ST.write state uu____213
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____222 = get_term_graph () in FStar_Unionfind.puf_id uu____222 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____228  ->
    let uu____229 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____229 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____237 = get_term_graph () in FStar_Unionfind.puf_find uu____237 u
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____247 =
        let uu____248 = get_term_graph () in
        FStar_Unionfind.puf_change uu____248 u (Some t) in
      set_term_graph uu____247
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____258 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____258 u v1
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____268 =
        let uu____269 = get_term_graph () in
        FStar_Unionfind.puf_union uu____269 u v1 in
      set_term_graph uu____268
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____275  -> let uu____276 = get () in uu____276.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___107_281 = get () in
      { term_graph = (uu___107_281.term_graph); univ_graph = ug } in
    let uu____282 =
      let uu___108_283 = FStar_ST.read state in
      { current = next; rest = (uu___108_283.rest) } in
    FStar_ST.write state uu____282
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____291 = get_univ_graph () in FStar_Unionfind.puf_id uu____291 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____297  ->
    let uu____298 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____298 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____306 = get_univ_graph () in FStar_Unionfind.puf_find uu____306 u
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____316 =
        let uu____317 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____317 u (Some t) in
      set_univ_graph uu____316
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____327 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____327 u v1
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____337 =
        let uu____338 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____338 u v1 in
      set_univ_graph uu____337