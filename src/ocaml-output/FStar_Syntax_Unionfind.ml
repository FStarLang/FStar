open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}
let vops: vops_t =
  let major = FStar_Util.mk_ref (Prims.parse_int "0") in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0") in
  let next_major uu____38 =
    FStar_ST.write minor (Prims.parse_int "0");
    (let uu____42 = FStar_Util.incr major; FStar_ST.read major in
     {
       FStar_Syntax_Syntax.major = uu____42;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____52 =
    let uu____53 = FStar_ST.read major in
    let uu____56 = FStar_Util.incr minor; FStar_ST.read minor in
    {
      FStar_Syntax_Syntax.major = uu____53;
      FStar_Syntax_Syntax.minor = uu____56
    } in
  { next_major; next_minor }
type tgraph = FStar_Syntax_Syntax.term option FStar_Unionfind.puf
type ugraph = FStar_Syntax_Syntax.universe option FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph;
  univ_graph: ugraph;
  version: FStar_Syntax_Syntax.version;}
let empty: FStar_Syntax_Syntax.version -> uf =
  fun v1  ->
    let uu____91 = FStar_Unionfind.puf_empty () in
    let uu____93 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____91; univ_graph = uu____93; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____98 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____99 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____98 uu____99
let state: uf FStar_ST.ref =
  let uu____102 = let uu____103 = vops.next_major () in empty uu____103 in
  FStar_Util.mk_ref uu____102
type tx =
  | TX of uf
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____117  -> FStar_ST.read state
let set: uf -> Prims.unit = fun u  -> FStar_ST.write state u
let reset: Prims.unit -> Prims.unit =
  fun uu____127  ->
    let v1 = vops.next_major () in let uu____129 = empty v1 in set uu____129
let new_transaction: Prims.unit -> tx =
  fun uu____132  ->
    let tx = let uu____134 = get () in TX uu____134 in
    (let uu____136 =
       let uu___99_137 = get () in
       let uu____138 = vops.next_minor () in
       {
         term_graph = (uu___99_137.term_graph);
         univ_graph = (uu___99_137.univ_graph);
         version = uu____138
       } in
     set uu____136);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____144  -> match uu____144 with | TX uf -> set uf
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____165  -> let uu____166 = get () in uu____166.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____169  -> let uu____170 = get () in uu____170.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____174 =
      let uu___100_175 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___100_175.univ_graph);
        version = (uu___100_175.version)
      } in
    set uu____174
let chk_v uu____184 =
  match uu____184 with
  | (u,v1) ->
      let expected = get_version () in
      if
        (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
          &&
          (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor)
      then u
      else
        (let uu____191 =
           let uu____192 = version_to_string expected in
           let uu____193 = version_to_string v1 in
           FStar_Util.format2
             "Incompatible version for unification variable: current version is %s; got version %s"
             uu____192 uu____193 in
         failwith uu____191)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____197 = get_term_graph () in
    let uu____200 = chk_v u in FStar_Unionfind.puf_id uu____197 uu____200
let fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)
  =
  fun uu____210  ->
    let uu____211 =
      let uu____214 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____214 None in
    let uu____218 = get_version () in (uu____211, uu____218)
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____225 = get_term_graph () in
    let uu____228 = chk_v u in FStar_Unionfind.puf_find uu____225 uu____228
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____242 =
        let uu____243 = get_term_graph () in
        let uu____246 = chk_v u in
        FStar_Unionfind.puf_change uu____243 uu____246 (Some t) in
      set_term_graph uu____242
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____260 = get_term_graph () in
      let uu____263 = chk_v u in
      let uu____270 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____260 uu____263 uu____270
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____284 =
        let uu____285 = get_term_graph () in
        let uu____288 = chk_v u in
        let uu____295 = chk_v v1 in
        FStar_Unionfind.puf_union uu____285 uu____288 uu____295 in
      set_term_graph uu____284
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____305  -> let uu____306 = get () in uu____306.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____310 =
      let uu___101_311 = get () in
      {
        term_graph = (uu___101_311.term_graph);
        univ_graph = ug;
        version = (uu___101_311.version)
      } in
    set uu____310
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____315 = get_univ_graph () in
    let uu____318 = chk_v u in FStar_Unionfind.puf_id uu____315 uu____318
let univ_fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)
  =
  fun uu____326  ->
    let uu____327 =
      let uu____330 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____330 None in
    let uu____334 = get_version () in (uu____327, uu____334)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____341 = get_univ_graph () in
    let uu____344 = chk_v u in FStar_Unionfind.puf_find uu____341 uu____344
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____356 =
        let uu____357 = get_univ_graph () in
        let uu____360 = chk_v u in
        FStar_Unionfind.puf_change uu____357 uu____360 (Some t) in
      set_univ_graph uu____356
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____372 = get_univ_graph () in
      let uu____375 = chk_v u in
      let uu____380 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____372 uu____375 uu____380
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____392 =
        let uu____393 = get_univ_graph () in
        let uu____396 = chk_v u in
        let uu____401 = chk_v v1 in
        FStar_Unionfind.puf_union uu____393 uu____396 uu____401 in
      set_univ_graph uu____392