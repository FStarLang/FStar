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
    let uu____55 = FStar_Unionfind.puf_empty () in
    let uu____57 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____55; univ_graph = uu____57 } in
  let tx_st = { current = init1; rest = [] } in FStar_Util.mk_ref tx_st
let get: Prims.unit -> uf =
  fun uu____65  -> let uu____66 = FStar_ST.read state in uu____66.current
let set: uf -> Prims.unit =
  fun u  ->
    let uu____72 =
      let uu___100_73 = FStar_ST.read state in
      { current = u; rest = (uu___100_73.rest) } in
    FStar_ST.write state uu____72
let reset: Prims.unit -> Prims.unit =
  fun uu____80  ->
    let uu____81 =
      let uu___101_82 = FStar_ST.read state in
      let uu____85 =
        let uu___102_86 =
          let uu____87 = FStar_ST.read state in uu____87.current in
        let uu____90 = FStar_Unionfind.puf_empty () in
        let uu____92 = FStar_Unionfind.puf_empty () in
        { term_graph = uu____90; univ_graph = uu____92 } in
      { current = uu____85; rest = (uu___101_82.rest) } in
    FStar_ST.write state uu____81
let new_transaction: Prims.unit -> tx =
  let tx_ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____101  ->
    let tx =
      FStar_Util.incr tx_ctr;
      (let uu____107 = FStar_ST.read tx_ctr in TX uu____107) in
    (let uu____111 =
       let uu___103_112 = FStar_ST.read state in
       let uu____115 =
         let uu____119 = let uu____122 = get () in (tx, uu____122) in
         let uu____123 =
           let uu____127 = FStar_ST.read state in uu____127.rest in
         uu____119 :: uu____123 in
       { current = (uu___103_112.current); rest = uu____115 } in
     FStar_ST.write state uu____111);
    tx
let commit_or_rollback: Prims.bool -> tx -> Prims.unit =
  fun rb  ->
    fun tx  ->
      let rec aux uu___99_146 =
        match uu___99_146 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____162 =
                  let uu___104_163 = FStar_ST.read state in
                  { current = (uu___104_163.current); rest } in
                FStar_ST.write state uu____162))
            else aux rest in
      let uu____169 = let uu____173 = FStar_ST.read state in uu____173.rest in
      aux uu____169
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____201  -> let uu____202 = get () in uu____202.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___105_207 = get () in
      { term_graph = tg; univ_graph = (uu___105_207.univ_graph) } in
    let uu____208 =
      let uu___106_209 = FStar_ST.read state in
      { current = next; rest = (uu___106_209.rest) } in
    FStar_ST.write state uu____208
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____217 = get_term_graph () in FStar_Unionfind.puf_id uu____217 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____223  ->
    let uu____224 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____224 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____232 = get_term_graph () in FStar_Unionfind.puf_find uu____232 u
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____242 =
        let uu____243 = get_term_graph () in
        FStar_Unionfind.puf_change uu____243 u (Some t) in
      set_term_graph uu____242
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____253 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____253 u v1
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____263 =
        let uu____264 = get_term_graph () in
        FStar_Unionfind.puf_union uu____264 u v1 in
      set_term_graph uu____263
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____270  -> let uu____271 = get () in uu____271.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___107_276 = get () in
      { term_graph = (uu___107_276.term_graph); univ_graph = ug } in
    let uu____277 =
      let uu___108_278 = FStar_ST.read state in
      { current = next; rest = (uu___108_278.rest) } in
    FStar_ST.write state uu____277
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____286 = get_univ_graph () in FStar_Unionfind.puf_id uu____286 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____292  ->
    let uu____293 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____293 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____301 = get_univ_graph () in FStar_Unionfind.puf_find uu____301 u
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____311 =
        let uu____312 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____312 u (Some t) in
      set_univ_graph uu____311
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____322 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____322 u v1
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____332 =
        let uu____333 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____333 u v1 in
      set_univ_graph uu____332