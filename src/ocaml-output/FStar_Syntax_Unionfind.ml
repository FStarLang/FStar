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
let new_transaction: Prims.unit -> tx =
  let tx_ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____83  ->
    let tx =
      FStar_Util.incr tx_ctr;
      (let uu____89 = FStar_ST.read tx_ctr in TX uu____89) in
    (let uu____93 =
       let uu___101_94 = FStar_ST.read state in
       let uu____97 =
         let uu____101 = let uu____104 = get () in (tx, uu____104) in
         let uu____105 =
           let uu____109 = FStar_ST.read state in uu____109.rest in
         uu____101 :: uu____105 in
       { current = (uu___101_94.current); rest = uu____97 } in
     FStar_ST.write state uu____93);
    tx
let commit_or_rollback: Prims.bool -> tx -> Prims.unit =
  fun rb  ->
    fun tx  ->
      let rec aux uu___99_128 =
        match uu___99_128 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____144 =
                  let uu___102_145 = FStar_ST.read state in
                  { current = (uu___102_145.current); rest } in
                FStar_ST.write state uu____144))
            else aux rest in
      let uu____151 = let uu____155 = FStar_ST.read state in uu____155.rest in
      aux uu____151
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____183  -> let uu____184 = get () in uu____184.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___103_189 = get () in
      { term_graph = tg; univ_graph = (uu___103_189.univ_graph) } in
    let uu____190 =
      let uu___104_191 = FStar_ST.read state in
      { current = next; rest = (uu___104_191.rest) } in
    FStar_ST.write state uu____190
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____199 = get_term_graph () in FStar_Unionfind.puf_id uu____199 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____205  ->
    let uu____206 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____206 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____214 = get_term_graph () in FStar_Unionfind.puf_find uu____214 u
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____224 =
        let uu____225 = get_term_graph () in
        FStar_Unionfind.puf_change uu____225 u (Some t) in
      set_term_graph uu____224
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____235 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____235 u v1
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____245 =
        let uu____246 = get_term_graph () in
        FStar_Unionfind.puf_union uu____246 u v1 in
      set_term_graph uu____245
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____252  -> let uu____253 = get () in uu____253.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___105_258 = get () in
      { term_graph = (uu___105_258.term_graph); univ_graph = ug } in
    let uu____259 =
      let uu___106_260 = FStar_ST.read state in
      { current = next; rest = (uu___106_260.rest) } in
    FStar_ST.write state uu____259
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____268 = get_univ_graph () in FStar_Unionfind.puf_id uu____268 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____274  ->
    let uu____275 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____275 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____283 = get_univ_graph () in FStar_Unionfind.puf_find uu____283 u
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____293 =
        let uu____294 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____294 u (Some t) in
      set_univ_graph uu____293
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____304 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____304 u v1
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____314 =
        let uu____315 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____315 u v1 in
      set_univ_graph uu____314