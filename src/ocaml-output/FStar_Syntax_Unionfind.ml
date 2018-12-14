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
  let next_major uu____80 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____126 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____126;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____211 =
    let uu____212 = FStar_ST.op_Bang major  in
    let uu____257 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____212;
      FStar_Syntax_Syntax.minor = uu____257
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
  version: FStar_Syntax_Syntax.version ;
  tc_cache:
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
      FStar_Syntax_Cache.cache
    }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; tc_cache;_} -> term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; tc_cache;_} -> univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; tc_cache;_} -> version
  
let (__proj__Mkuf__item__tc_cache :
  uf ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
      FStar_Syntax_Cache.cache)
  =
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; tc_cache;_} -> tc_cache
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____456 = FStar_Unionfind.puf_empty ()  in
    let uu____459 = FStar_Unionfind.puf_empty ()  in
    let uu____462 = FStar_Syntax_Cache.create ()  in
    {
      term_graph = uu____456;
      univ_graph = uu____459;
      version = v1;
      tc_cache = uu____462
    }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____486 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____488 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____486 uu____488
  
let (state : uf FStar_ST.ref) =
  let uu____505 = let uu____506 = vops.next_major ()  in empty uu____506  in
  FStar_Util.mk_ref uu____505 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____532  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____582  ->
    let v1 = vops.next_major ()  in
    let uu____584 = empty v1  in set uu____584
  
let (new_transaction : unit -> tx) =
  fun uu____590  ->
    let tx = let uu____592 = get ()  in TX uu____592  in
    (let uu____594 =
       let uu___87_595 = get ()  in
       let uu____596 = vops.next_minor ()  in
       {
         term_graph = (uu___87_595.term_graph);
         univ_graph = (uu___87_595.univ_graph);
         version = uu____596;
         tc_cache = (uu___87_595.tc_cache)
       }  in
     set uu____594);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____608  -> match uu____608 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____670  -> let uu____671 = get ()  in uu____671.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____677  -> let uu____678 = get ()  in uu____678.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____685 =
      let uu___88_686 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___88_686.univ_graph);
        version = (uu___88_686.version);
        tc_cache = (uu___88_686.tc_cache)
      }  in
    set uu____685
  
let chk_v :
  'Auu____692 . ('Auu____692 * FStar_Syntax_Syntax.version) -> 'Auu____692 =
  fun uu____701  ->
    match uu____701 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____713 =
             let uu____715 = version_to_string expected  in
             let uu____717 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____715 uu____717
              in
           failwith uu____713)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____727 = get_term_graph ()  in
    let uu____732 = chk_v u  in FStar_Unionfind.puf_id uu____727 uu____732
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____753 =
      let uu____760 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____760 n1  in
    let uu____767 = get_version ()  in (uu____753, uu____767)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____779  ->
    let uu____780 =
      let uu____787 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____787 FStar_Pervasives_Native.None  in
    let uu____794 = get_version ()  in (uu____780, uu____794)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____809 = get_term_graph ()  in
    let uu____814 = chk_v u  in FStar_Unionfind.puf_find uu____809 uu____814
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____838 =
        let uu____839 = get_term_graph ()  in
        let uu____844 = chk_v u  in
        FStar_Unionfind.puf_change uu____839 uu____844
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____838
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____869 = get_term_graph ()  in
      let uu____874 = chk_v u  in
      let uu____885 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____869 uu____874 uu____885
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____909 =
        let uu____910 = get_term_graph ()  in
        let uu____915 = chk_v u  in
        let uu____926 = chk_v v1  in
        FStar_Unionfind.puf_union uu____910 uu____915 uu____926  in
      set_term_graph uu____909
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____944  -> let uu____945 = get ()  in uu____945.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____952 =
      let uu___89_953 = get ()  in
      {
        term_graph = (uu___89_953.term_graph);
        univ_graph = ug;
        version = (uu___89_953.version);
        tc_cache = (uu___89_953.tc_cache)
      }  in
    set uu____952
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____961 = get_univ_graph ()  in
    let uu____966 = chk_v u  in FStar_Unionfind.puf_id uu____961 uu____966
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____985 =
      let uu____990 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____990 n1  in
    let uu____997 = get_version ()  in (uu____985, uu____997)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____1007  ->
    let uu____1008 =
      let uu____1013 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____1013 FStar_Pervasives_Native.None  in
    let uu____1020 = get_version ()  in (uu____1008, uu____1020)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____1033 = get_univ_graph ()  in
    let uu____1038 = chk_v u  in
    FStar_Unionfind.puf_find uu____1033 uu____1038
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____1060 =
        let uu____1061 = get_univ_graph ()  in
        let uu____1066 = chk_v u  in
        FStar_Unionfind.puf_change uu____1061 uu____1066
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____1060
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____1089 = get_univ_graph ()  in
      let uu____1094 = chk_v u  in
      let uu____1103 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____1089 uu____1094 uu____1103
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____1125 =
        let uu____1126 = get_univ_graph ()  in
        let uu____1131 = chk_v u  in
        let uu____1140 = chk_v v1  in
        FStar_Unionfind.puf_union uu____1126 uu____1131 uu____1140  in
      set_univ_graph uu____1125
  
let (cache_tc :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) -> unit)
  =
  fun e  ->
    fun t  ->
      let uu____1170 = let uu____1177 = get ()  in uu____1177.tc_cache  in
      FStar_Syntax_Cache.add uu____1170 e t
  
let (query_tc :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun f_opt  ->
      let uu____1217 = let uu____1224 = get ()  in uu____1224.tc_cache  in
      FStar_Syntax_Cache.find uu____1217 e f_opt
  