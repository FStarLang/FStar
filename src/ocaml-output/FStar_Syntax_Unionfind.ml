open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}
let vops: vops_t =
  let major = FStar_Util.mk_ref (Prims.parse_int "0") in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0") in
  let next_major uu____42 =
    FStar_ST.write minor (Prims.parse_int "0");
    (let uu____46 = FStar_Util.incr major; FStar_ST.read major in
     {
       FStar_Syntax_Syntax.major = uu____46;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____56 =
    let uu____57 = FStar_ST.read major in
    let uu____60 = FStar_Util.incr minor; FStar_ST.read minor in
    {
      FStar_Syntax_Syntax.major = uu____57;
      FStar_Syntax_Syntax.minor = uu____60
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
    let uu____98 = FStar_Unionfind.puf_empty () in
    let uu____100 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____98; univ_graph = uu____100; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____105 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____106 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____105 uu____106
let state: uf FStar_ST.ref =
  let uu____109 = let uu____110 = vops.next_major () in empty uu____110 in
  FStar_Util.mk_ref uu____109
type tx =
  | TX of uf
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____125  -> FStar_ST.read state
let set: uf -> Prims.unit = fun u  -> FStar_ST.write state u
let reset: Prims.unit -> Prims.unit =
  fun uu____135  ->
    let v1 = vops.next_major () in let uu____137 = empty v1 in set uu____137
let new_transaction: Prims.unit -> tx =
  fun uu____140  ->
    let tx = let uu____142 = get () in TX uu____142 in
    (let uu____144 =
       let uu___99_145 = get () in
       let uu____146 = vops.next_minor () in
       {
         term_graph = (uu___99_145.term_graph);
         univ_graph = (uu___99_145.univ_graph);
         version = uu____146
       } in
     set uu____144);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____152  -> match uu____152 with | TX uf -> set uf
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____173  -> let uu____174 = get () in uu____174.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____177  -> let uu____178 = get () in uu____178.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____182 =
      let uu___100_183 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___100_183.univ_graph);
        version = (uu___100_183.version)
      } in
    set uu____182
let chk_v uu____192 =
  match uu____192 with
  | (u,v1) ->
      let expected = get_version () in
      if
        (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
          &&
          (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor)
      then u
      else
        (let uu____199 =
           let uu____200 = version_to_string expected in
           let uu____201 = version_to_string v1 in
           FStar_Util.format2
             "Incompatible version for unification variable: current version is %s; got version %s"
             uu____200 uu____201 in
         failwith uu____199)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____205 = get_term_graph () in
    let uu____208 = chk_v u in FStar_Unionfind.puf_id uu____205 uu____208
let fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)
  =
  fun uu____218  ->
    let uu____219 =
      let uu____222 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____222 None in
    let uu____226 = get_version () in (uu____219, uu____226)
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____233 = get_term_graph () in
    let uu____236 = chk_v u in FStar_Unionfind.puf_find uu____233 uu____236
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____250 =
        let uu____251 = get_term_graph () in
        let uu____254 = chk_v u in
        FStar_Unionfind.puf_change uu____251 uu____254 (Some t) in
      set_term_graph uu____250
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____268 = get_term_graph () in
      let uu____271 = chk_v u in
      let uu____278 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____268 uu____271 uu____278
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____292 =
        let uu____293 = get_term_graph () in
        let uu____296 = chk_v u in
        let uu____303 = chk_v v1 in
        FStar_Unionfind.puf_union uu____293 uu____296 uu____303 in
      set_term_graph uu____292
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____313  -> let uu____314 = get () in uu____314.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____318 =
      let uu___101_319 = get () in
      {
        term_graph = (uu___101_319.term_graph);
        univ_graph = ug;
        version = (uu___101_319.version)
      } in
    set uu____318
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____323 = get_univ_graph () in
    let uu____326 = chk_v u in FStar_Unionfind.puf_id uu____323 uu____326
let univ_fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)
  =
  fun uu____334  ->
    let uu____335 =
      let uu____338 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____338 None in
    let uu____342 = get_version () in (uu____335, uu____342)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____349 = get_univ_graph () in
    let uu____352 = chk_v u in FStar_Unionfind.puf_find uu____349 uu____352
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____364 =
        let uu____365 = get_univ_graph () in
        let uu____368 = chk_v u in
        FStar_Unionfind.puf_change uu____365 uu____368 (Some t) in
      set_univ_graph uu____364
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____380 = get_univ_graph () in
      let uu____383 = chk_v u in
      let uu____388 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____380 uu____383 uu____388
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____400 =
        let uu____401 = get_univ_graph () in
        let uu____404 = chk_v u in
        let uu____409 = chk_v v1 in
        FStar_Unionfind.puf_union uu____401 uu____404 uu____409 in
      set_univ_graph uu____400