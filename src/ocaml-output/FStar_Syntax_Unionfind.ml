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
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____82 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____82;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____132 =
    let uu____133 = FStar_ST.op_Bang major in
    let uu____158 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____133;
      FStar_Syntax_Syntax.minor = uu____158
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
    let uu____250 = FStar_Unionfind.puf_empty () in
    let uu____253 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____250; univ_graph = uu____253; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____260 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____261 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____260 uu____261
let state: uf FStar_ST.ref =
  let uu____271 = let uu____272 = vops.next_major () in empty uu____272 in
  FStar_Util.mk_ref uu____271
type tx =
  | TX of uf
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____289  -> FStar_ST.op_Bang state
let set: uf -> Prims.unit = fun u  -> FStar_ST.op_Colon_Equals state u
let reset: Prims.unit -> Prims.unit =
  fun uu____317  ->
    let v1 = vops.next_major () in let uu____319 = empty v1 in set uu____319
let new_transaction: Prims.unit -> tx =
  fun uu____323  ->
    let tx = let uu____325 = get () in TX uu____325 in
    (let uu____327 =
       let uu___100_328 = get () in
       let uu____329 = vops.next_minor () in
       {
         term_graph = (uu___100_328.term_graph);
         univ_graph = (uu___100_328.univ_graph);
         version = uu____329
       } in
     set uu____327);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____337  -> match uu____337 with | TX uf -> set uf
let update_in_tx: 'a . 'a FStar_ST.ref -> 'a -> Prims.unit =
  fun r  -> fun x  -> ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____382  -> let uu____383 = get () in uu____383.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____387  -> let uu____388 = get () in uu____388.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____393 =
      let uu___101_394 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___101_394.univ_graph);
        version = (uu___101_394.version)
      } in
    set uu____393
let chk_v:
  'Auu____399 .
    ('Auu____399,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____399
  =
  fun uu____407  ->
    match uu____407 with
    | (u,v1) ->
        let expected = get_version () in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____416 =
             let uu____417 = version_to_string expected in
             let uu____418 = version_to_string v1 in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____417 uu____418 in
           failwith uu____416)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____423 = get_term_graph () in
    let uu____428 = chk_v u in FStar_Unionfind.puf_id uu____423 uu____428
let from_id: Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____445 =
      let uu____450 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____450 n1 in
    let uu____457 = get_version () in (uu____445, uu____457)
let fresh: Prims.unit -> FStar_Syntax_Syntax.uvar =
  fun uu____465  ->
    let uu____466 =
      let uu____471 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____471 FStar_Pervasives_Native.None in
    let uu____478 = get_version () in (uu____466, uu____478)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____489 = get_term_graph () in
    let uu____494 = chk_v u in FStar_Unionfind.puf_find uu____489 uu____494
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____515 =
        let uu____516 = get_term_graph () in
        let uu____521 = chk_v u in
        FStar_Unionfind.puf_change uu____516 uu____521
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____515
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____542 = get_term_graph () in
      let uu____547 = chk_v u in
      let uu____558 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____542 uu____547 uu____558
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____579 =
        let uu____580 = get_term_graph () in
        let uu____585 = chk_v u in
        let uu____596 = chk_v v1 in
        FStar_Unionfind.puf_union uu____580 uu____585 uu____596 in
      set_term_graph uu____579
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____612  -> let uu____613 = get () in uu____613.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____618 =
      let uu___102_619 = get () in
      {
        term_graph = (uu___102_619.term_graph);
        univ_graph = ug;
        version = (uu___102_619.version)
      } in
    set uu____618
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____624 = get_univ_graph () in
    let uu____629 = chk_v u in FStar_Unionfind.puf_id uu____624 uu____629
let univ_from_id: Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____644 =
      let uu____649 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____649 n1 in
    let uu____656 = get_version () in (uu____644, uu____656)
let univ_fresh: Prims.unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____664  ->
    let uu____665 =
      let uu____670 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____670 FStar_Pervasives_Native.None in
    let uu____677 = get_version () in (uu____665, uu____677)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____688 = get_univ_graph () in
    let uu____693 = chk_v u in FStar_Unionfind.puf_find uu____688 uu____693
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____712 =
        let uu____713 = get_univ_graph () in
        let uu____718 = chk_v u in
        FStar_Unionfind.puf_change uu____713 uu____718
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____712
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____737 = get_univ_graph () in
      let uu____742 = chk_v u in
      let uu____751 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____737 uu____742 uu____751
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____770 =
        let uu____771 = get_univ_graph () in
        let uu____776 = chk_v u in
        let uu____785 = chk_v v1 in
        FStar_Unionfind.puf_union uu____771 uu____776 uu____785 in
      set_univ_graph uu____770