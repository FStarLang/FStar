open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { next_major; next_minor;_} -> next_major
  
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { next_major; next_minor;_} -> next_minor
  
let (vops : vops_t) =
  let major = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let next_major uu____41992 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____42038 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____42038;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____42123 =
    let uu____42124 = FStar_ST.op_Bang major  in
    let uu____42169 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____42124;
      FStar_Syntax_Syntax.minor = uu____42169
    }  in
  { next_major; next_minor } 
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> version
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____42304 = FStar_Unionfind.puf_empty ()  in
    let uu____42307 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____42304; univ_graph = uu____42307; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____42317 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____42319 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____42317 uu____42319
  
let (state : uf FStar_ST.ref) =
  let uu____42336 =
    let uu____42337 = vops.next_major ()  in empty uu____42337  in
  FStar_Util.mk_ref uu____42336 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____42363  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____42413  ->
    let v1 = vops.next_major ()  in
    let uu____42415 = empty v1  in set uu____42415
  
let (new_transaction : unit -> tx) =
  fun uu____42421  ->
    let tx = let uu____42423 = get ()  in TX uu____42423  in
    (let uu____42425 =
       let uu___425_42426 = get ()  in
       let uu____42427 = vops.next_minor ()  in
       {
         term_graph = (uu___425_42426.term_graph);
         univ_graph = (uu___425_42426.univ_graph);
         version = uu____42427
       }  in
     set uu____42425);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____42439  -> match uu____42439 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____42501  -> let uu____42502 = get ()  in uu____42502.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____42508  -> let uu____42509 = get ()  in uu____42509.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____42516 =
      let uu___438_42517 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_42517.univ_graph);
        version = (uu___438_42517.version)
      }  in
    set uu____42516
  
let chk_v :
  'Auu____42523 .
    ('Auu____42523 * FStar_Syntax_Syntax.version) -> 'Auu____42523
  =
  fun uu____42532  ->
    match uu____42532 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____42544 =
             let uu____42546 = version_to_string expected  in
             let uu____42548 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____42546 uu____42548
              in
           failwith uu____42544)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____42558 = get_term_graph ()  in
    let uu____42563 = chk_v u  in
    FStar_Unionfind.puf_id uu____42558 uu____42563
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____42584 =
      let uu____42591 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____42591 n1  in
    let uu____42598 = get_version ()  in (uu____42584, uu____42598)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____42610  ->
    let uu____42611 =
      let uu____42618 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____42618 FStar_Pervasives_Native.None  in
    let uu____42625 = get_version ()  in (uu____42611, uu____42625)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42640 = get_term_graph ()  in
    let uu____42645 = chk_v u  in
    FStar_Unionfind.puf_find uu____42640 uu____42645
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____42669 =
        let uu____42670 = get_term_graph ()  in
        let uu____42675 = chk_v u  in
        FStar_Unionfind.puf_change uu____42670 uu____42675
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____42669
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____42700 = get_term_graph ()  in
      let uu____42705 = chk_v u  in
      let uu____42716 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42700 uu____42705 uu____42716
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____42740 =
        let uu____42741 = get_term_graph ()  in
        let uu____42746 = chk_v u  in
        let uu____42757 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42741 uu____42746 uu____42757  in
      set_term_graph uu____42740
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____42775  -> let uu____42776 = get ()  in uu____42776.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____42783 =
      let uu___457_42784 = get ()  in
      {
        term_graph = (uu___457_42784.term_graph);
        univ_graph = ug;
        version = (uu___457_42784.version)
      }  in
    set uu____42783
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____42792 = get_univ_graph ()  in
    let uu____42797 = chk_v u  in
    FStar_Unionfind.puf_id uu____42792 uu____42797
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____42816 =
      let uu____42821 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____42821 n1  in
    let uu____42828 = get_version ()  in (uu____42816, uu____42828)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____42838  ->
    let uu____42839 =
      let uu____42844 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____42844 FStar_Pervasives_Native.None  in
    let uu____42851 = get_version ()  in (uu____42839, uu____42851)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42864 = get_univ_graph ()  in
    let uu____42869 = chk_v u  in
    FStar_Unionfind.puf_find uu____42864 uu____42869
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____42891 =
        let uu____42892 = get_univ_graph ()  in
        let uu____42897 = chk_v u  in
        FStar_Unionfind.puf_change uu____42892 uu____42897
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____42891
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____42920 = get_univ_graph ()  in
      let uu____42925 = chk_v u  in
      let uu____42934 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42920 uu____42925 uu____42934
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____42956 =
        let uu____42957 = get_univ_graph ()  in
        let uu____42962 = chk_v u  in
        let uu____42971 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42957 uu____42962 uu____42971  in
      set_univ_graph uu____42956
  