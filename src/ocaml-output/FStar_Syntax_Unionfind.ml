open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }[@@deriving show]
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
  
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
  
let (vops : vops_t) =
  let major = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let next_major uu____68 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____115 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____115;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____200 =
    let uu____201 = FStar_ST.op_Bang major  in
    let uu____247 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____201;
      FStar_Syntax_Syntax.minor = uu____247
    }  in
  { next_major; next_minor } 
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
[@@deriving show]
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf[@@deriving show]
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version }[@@deriving show]
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____376 = FStar_Unionfind.puf_empty ()  in
    let uu____379 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____376; univ_graph = uu____379; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____387 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____388 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____387 uu____388
  
let (state : uf FStar_ST.ref) =
  let uu____402 = let uu____403 = vops.next_major ()  in empty uu____403  in
  FStar_Util.mk_ref uu____402 
type tx =
  | TX of uf [@@deriving show]
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____423  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____479  ->
    let v1 = vops.next_major ()  in
    let uu____481 = empty v1  in set uu____481
  
let (new_transaction : unit -> tx) =
  fun uu____486  ->
    let tx = let uu____488 = get ()  in TX uu____488  in
    (let uu____490 =
       let uu___25_491 = get ()  in
       let uu____492 = vops.next_minor ()  in
       {
         term_graph = (uu___25_491.term_graph);
         univ_graph = (uu___25_491.univ_graph);
         version = uu____492
       }  in
     set uu____490);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____502  -> match uu____502 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____562  -> let uu____563 = get ()  in uu____563.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____568  -> let uu____569 = get ()  in uu____569.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____575 =
      let uu___26_576 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___26_576.univ_graph);
        version = (uu___26_576.version)
      }  in
    set uu____575
  
let chk_v :
  'Auu____581 .
    ('Auu____581,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____581
  =
  fun uu____590  ->
    match uu____590 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____599 =
             let uu____600 = version_to_string expected  in
             let uu____601 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____600 uu____601
              in
           failwith uu____599)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____607 = get_term_graph ()  in
    let uu____612 = chk_v u  in FStar_Unionfind.puf_id uu____607 uu____612
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____630 =
      let uu____635 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____635 n1  in
    let uu____642 = get_version ()  in (uu____630, uu____642)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____651  ->
    let uu____652 =
      let uu____657 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____657 FStar_Pervasives_Native.None  in
    let uu____664 = get_version ()  in (uu____652, uu____664)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____676 = get_term_graph ()  in
    let uu____681 = chk_v u  in FStar_Unionfind.puf_find uu____676 uu____681
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____704 =
        let uu____705 = get_term_graph ()  in
        let uu____710 = chk_v u  in
        FStar_Unionfind.puf_change uu____705 uu____710
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____704
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____733 = get_term_graph ()  in
      let uu____738 = chk_v u  in
      let uu____749 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____733 uu____738 uu____749
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____772 =
        let uu____773 = get_term_graph ()  in
        let uu____778 = chk_v u  in
        let uu____789 = chk_v v1  in
        FStar_Unionfind.puf_union uu____773 uu____778 uu____789  in
      set_term_graph uu____772
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____806  -> let uu____807 = get ()  in uu____807.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____813 =
      let uu___27_814 = get ()  in
      {
        term_graph = (uu___27_814.term_graph);
        univ_graph = ug;
        version = (uu___27_814.version)
      }  in
    set uu____813
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____820 = get_univ_graph ()  in
    let uu____825 = chk_v u  in FStar_Unionfind.puf_id uu____820 uu____825
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____841 =
      let uu____846 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____846 n1  in
    let uu____853 = get_version ()  in (uu____841, uu____853)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____862  ->
    let uu____863 =
      let uu____868 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____868 FStar_Pervasives_Native.None  in
    let uu____875 = get_version ()  in (uu____863, uu____875)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____887 = get_univ_graph ()  in
    let uu____892 = chk_v u  in FStar_Unionfind.puf_find uu____887 uu____892
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____913 =
        let uu____914 = get_univ_graph ()  in
        let uu____919 = chk_v u  in
        FStar_Unionfind.puf_change uu____914 uu____919
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____913
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____940 = get_univ_graph ()  in
      let uu____945 = chk_v u  in
      let uu____954 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____940 uu____945 uu____954
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____975 =
        let uu____976 = get_univ_graph ()  in
        let uu____981 = chk_v u  in
        let uu____990 = chk_v v1  in
        FStar_Unionfind.puf_union uu____976 uu____981 uu____990  in
      set_univ_graph uu____975
  