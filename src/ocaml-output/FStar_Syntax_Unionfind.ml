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
    let uu____66 = FStar_Unionfind.puf_empty () in
    let uu____68 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____66; univ_graph = uu____68 } in
  let tx_st = { current = init1; rest = [] } in FStar_Util.mk_ref tx_st
let get: Prims.unit -> uf =
  fun uu____77  -> let uu____78 = FStar_ST.read state in uu____78.current
let set: uf -> Prims.unit =
  fun u  ->
    let uu____85 =
      let uu___101_86 = FStar_ST.read state in
      { current = u; rest = (uu___101_86.rest) } in
    FStar_ST.write state uu____85
let reset: Prims.unit -> Prims.unit =
  fun uu____94  ->
    let uu____95 =
      let uu___102_96 = FStar_ST.read state in
      let uu____99 =
        let uu___103_100 =
          let uu____101 = FStar_ST.read state in uu____101.current in
        let uu____104 = FStar_Unionfind.puf_empty () in
        let uu____106 = FStar_Unionfind.puf_empty () in
        { term_graph = uu____104; univ_graph = uu____106 } in
      { current = uu____99; rest = (uu___102_96.rest) } in
    FStar_ST.write state uu____95
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
      let rec aux uu___100_163 =
        match uu___100_163 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____179 =
                  let uu___105_180 = FStar_ST.read state in
                  { current = (uu___105_180.current); rest } in
                FStar_ST.write state uu____179))
            else aux rest in
      let uu____186 = let uu____190 = FStar_ST.read state in uu____190.rest in
      aux uu____186
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____224  -> let uu____225 = get () in uu____225.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___106_231 = get () in
      { term_graph = tg; univ_graph = (uu___106_231.univ_graph) } in
    let uu____232 =
      let uu___107_233 = FStar_ST.read state in
      { current = next; rest = (uu___107_233.rest) } in
    FStar_ST.write state uu____232
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____242 = get_term_graph () in FStar_Unionfind.puf_id uu____242 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____249  ->
    let uu____250 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____250 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____259 = get_term_graph () in FStar_Unionfind.puf_find uu____259 u
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____271 =
        let uu____272 = get_term_graph () in
        FStar_Unionfind.puf_change uu____272 u (Some t) in
      set_term_graph uu____271
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____284 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____284 u v1
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____296 =
        let uu____297 = get_term_graph () in
        FStar_Unionfind.puf_union uu____297 u v1 in
      set_term_graph uu____296
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____304  -> let uu____305 = get () in uu____305.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___108_311 = get () in
      { term_graph = (uu___108_311.term_graph); univ_graph = ug } in
    let uu____312 =
      let uu___109_313 = FStar_ST.read state in
      { current = next; rest = (uu___109_313.rest) } in
    FStar_ST.write state uu____312
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____322 = get_univ_graph () in FStar_Unionfind.puf_id uu____322 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____329  ->
    let uu____330 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____330 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____339 = get_univ_graph () in FStar_Unionfind.puf_find uu____339 u
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____351 =
        let uu____352 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____352 u (Some t) in
      set_univ_graph uu____351
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____364 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____364 u v1
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____376 =
        let uu____377 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____377 u v1 in
      set_univ_graph uu____376