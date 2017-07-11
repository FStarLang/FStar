open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}
let __proj__Mkvops_t__item__next_major:
  vops_t -> Prims.unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
let __proj__Mkvops_t__item__next_minor:
  vops_t -> Prims.unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
let vops: vops_t =
  let major = FStar_Util.mk_ref (Prims.parse_int "0") in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0") in
  let next_major uu____56 =
    FStar_ST.write minor (Prims.parse_int "0");
    (let uu____60 = FStar_Util.incr major; FStar_ST.read major in
     {
       FStar_Syntax_Syntax.major = uu____60;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____70 =
    let uu____71 = FStar_ST.read major in
    let uu____74 = FStar_Util.incr minor; FStar_ST.read minor in
    {
      FStar_Syntax_Syntax.major = uu____71;
      FStar_Syntax_Syntax.minor = uu____74
    } in
  { next_major; next_minor }
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph;
  univ_graph: ugraph;
  version: FStar_Syntax_Syntax.version;}
let __proj__Mkuf__item__term_graph: uf -> tgraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
let __proj__Mkuf__item__univ_graph: uf -> ugraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
let __proj__Mkuf__item__version: uf -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
let empty: FStar_Syntax_Syntax.version -> uf =
  fun v1  ->
    let uu____122 = FStar_Unionfind.puf_empty () in
    let uu____124 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____122; univ_graph = uu____124; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____130 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____131 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____130 uu____131
let state: uf FStar_ST.ref =
  let uu____134 = let uu____135 = vops.next_major () in empty uu____135 in
  FStar_Util.mk_ref uu____134
type tx =
  | TX of uf
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____153  -> FStar_ST.read state
let set: uf -> Prims.unit = fun u  -> FStar_ST.write state u
let reset: Prims.unit -> Prims.unit =
  fun uu____165  ->
    let v1 = vops.next_major () in let uu____167 = empty v1 in set uu____167
let new_transaction: Prims.unit -> tx =
  fun uu____171  ->
    let tx = let uu____173 = get () in TX uu____173 in
    (let uu____175 =
       let uu___100_176 = get () in
       let uu____177 = vops.next_minor () in
       {
         term_graph = (uu___100_176.term_graph);
         univ_graph = (uu___100_176.univ_graph);
         version = uu____177
       } in
     set uu____175);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____185  -> match uu____185 with | TX uf -> set uf
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____210  -> let uu____211 = get () in uu____211.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____215  -> let uu____216 = get () in uu____216.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____221 =
      let uu___101_222 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___101_222.univ_graph);
        version = (uu___101_222.version)
      } in
    set uu____221
let chk_v uu____233 =
  match uu____233 with
  | (u,v1) ->
      let expected = get_version () in
      if
        (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
          &&
          (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor)
      then u
      else
        (let uu____240 =
           let uu____241 = version_to_string expected in
           let uu____242 = version_to_string v1 in
           FStar_Util.format2
             "Incompatible version for unification variable: current version is %s; got version %s"
             uu____241 uu____242 in
         failwith uu____240)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____247 = get_term_graph () in
    let uu____250 = chk_v u in FStar_Unionfind.puf_id uu____247 uu____250
let from_id:
  Prims.int ->
    (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    let uu____261 =
      let uu____264 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____264 n1 in
    let uu____268 = get_version () in (uu____261, uu____268)
let fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____274  ->
    let uu____275 =
      let uu____278 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____278 FStar_Pervasives_Native.None in
    let uu____282 = get_version () in (uu____275, uu____282)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____290 = get_term_graph () in
    let uu____293 = chk_v u in FStar_Unionfind.puf_find uu____290 uu____293
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____308 =
        let uu____309 = get_term_graph () in
        let uu____312 = chk_v u in
        FStar_Unionfind.puf_change uu____309 uu____312
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____308
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____327 = get_term_graph () in
      let uu____330 = chk_v u in
      let uu____336 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____327 uu____330 uu____336
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____351 =
        let uu____352 = get_term_graph () in
        let uu____355 = chk_v u in
        let uu____361 = chk_v v1 in
        FStar_Unionfind.puf_union uu____352 uu____355 uu____361 in
      set_term_graph uu____351
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____371  -> let uu____372 = get () in uu____372.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____377 =
      let uu___102_378 = get () in
      {
        term_graph = (uu___102_378.term_graph);
        univ_graph = ug;
        version = (uu___102_378.version)
      } in
    set uu____377
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____383 = get_univ_graph () in
    let uu____386 = chk_v u in FStar_Unionfind.puf_id uu____383 uu____386
let univ_from_id:
  Prims.int ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    let uu____396 =
      let uu____399 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____399 n1 in
    let uu____403 = get_version () in (uu____396, uu____403)
let univ_fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____409  ->
    let uu____410 =
      let uu____413 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____413 FStar_Pervasives_Native.None in
    let uu____417 = get_version () in (uu____410, uu____417)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____425 = get_univ_graph () in
    let uu____428 = chk_v u in FStar_Unionfind.puf_find uu____425 uu____428
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____442 =
        let uu____443 = get_univ_graph () in
        let uu____446 = chk_v u in
        FStar_Unionfind.puf_change uu____443 uu____446
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____442
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____460 = get_univ_graph () in
      let uu____463 = chk_v u in
      let uu____468 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____460 uu____463 uu____468
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____482 =
        let uu____483 = get_univ_graph () in
        let uu____486 = chk_v u in
        let uu____491 = chk_v v1 in
        FStar_Unionfind.puf_union uu____483 uu____486 uu____491 in
      set_univ_graph uu____482