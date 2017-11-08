open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}[@@deriving show]
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
  let next_major uu____52 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____114 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____114;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____200 =
    let uu____201 = FStar_ST.op_Bang major in
    let uu____262 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____201;
      FStar_Syntax_Syntax.minor = uu____262
    } in
  { next_major; next_minor }
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
[@@deriving show]
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf[@@deriving show]
type uf =
  {
  term_graph: tgraph;
  univ_graph: ugraph;
  version: FStar_Syntax_Syntax.version;}[@@deriving show]
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
    let uu____386 = FStar_Unionfind.puf_empty () in
    let uu____389 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____386; univ_graph = uu____389; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____395 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____396 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____395 uu____396
let state: uf FStar_ST.ref =
  let uu____406 = let uu____407 = vops.next_major () in empty uu____407 in
  FStar_Util.mk_ref uu____406
type tx =
  | TX of uf[@@deriving show]
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____421  -> FStar_ST.op_Bang state
let set: uf -> Prims.unit = fun u  -> FStar_ST.op_Colon_Equals state u
let reset: Prims.unit -> Prims.unit =
  fun uu____519  ->
    let v1 = vops.next_major () in let uu____521 = empty v1 in set uu____521
let new_transaction: Prims.unit -> tx =
  fun uu____524  ->
    let tx = let uu____526 = get () in TX uu____526 in
    (let uu____528 =
       let uu___147_529 = get () in
       let uu____530 = vops.next_minor () in
       {
         term_graph = (uu___147_529.term_graph);
         univ_graph = (uu___147_529.univ_graph);
         version = uu____530
       } in
     set uu____528);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____536  -> match uu____536 with | TX uf -> set uf
let update_in_tx: 'a . 'a FStar_ST.ref -> 'a -> Prims.unit =
  fun r  -> fun x  -> ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____577  -> let uu____578 = get () in uu____578.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____581  -> let uu____582 = get () in uu____582.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____586 =
      let uu___148_587 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___148_587.univ_graph);
        version = (uu___148_587.version)
      } in
    set uu____586
let chk_v:
  'Auu____590 .
    ('Auu____590,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____590
  =
  fun uu____598  ->
    match uu____598 with
    | (u,v1) ->
        let expected = get_version () in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____607 =
             let uu____608 = version_to_string expected in
             let uu____609 = version_to_string v1 in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____608 uu____609 in
           failwith uu____607)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____613 = get_term_graph () in
    let uu____618 = chk_v u in FStar_Unionfind.puf_id uu____613 uu____618
let from_id: Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____634 =
      let uu____639 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____639 n1 in
    let uu____646 = get_version () in (uu____634, uu____646)
let fresh: Prims.unit -> FStar_Syntax_Syntax.uvar =
  fun uu____653  ->
    let uu____654 =
      let uu____659 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____659 FStar_Pervasives_Native.None in
    let uu____666 = get_version () in (uu____654, uu____666)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____676 = get_term_graph () in
    let uu____681 = chk_v u in FStar_Unionfind.puf_find uu____676 uu____681
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____700 =
        let uu____701 = get_term_graph () in
        let uu____706 = chk_v u in
        FStar_Unionfind.puf_change uu____701 uu____706
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____700
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____725 = get_term_graph () in
      let uu____730 = chk_v u in
      let uu____741 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____725 uu____730 uu____741
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____760 =
        let uu____761 = get_term_graph () in
        let uu____766 = chk_v u in
        let uu____777 = chk_v v1 in
        FStar_Unionfind.puf_union uu____761 uu____766 uu____777 in
      set_term_graph uu____760
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____792  -> let uu____793 = get () in uu____793.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____797 =
      let uu___149_798 = get () in
      {
        term_graph = (uu___149_798.term_graph);
        univ_graph = ug;
        version = (uu___149_798.version)
      } in
    set uu____797
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____802 = get_univ_graph () in
    let uu____807 = chk_v u in FStar_Unionfind.puf_id uu____802 uu____807
let univ_from_id: Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____821 =
      let uu____826 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____826 n1 in
    let uu____833 = get_version () in (uu____821, uu____833)
let univ_fresh: Prims.unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____840  ->
    let uu____841 =
      let uu____846 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____846 FStar_Pervasives_Native.None in
    let uu____853 = get_version () in (uu____841, uu____853)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____863 = get_univ_graph () in
    let uu____868 = chk_v u in FStar_Unionfind.puf_find uu____863 uu____868
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____885 =
        let uu____886 = get_univ_graph () in
        let uu____891 = chk_v u in
        FStar_Unionfind.puf_change uu____886 uu____891
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____885
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____908 = get_univ_graph () in
      let uu____913 = chk_v u in
      let uu____922 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____908 uu____913 uu____922
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____939 =
        let uu____940 = get_univ_graph () in
        let uu____945 = chk_v u in
        let uu____954 = chk_v v1 in
        FStar_Unionfind.puf_union uu____940 uu____945 uu____954 in
      set_univ_graph uu____939