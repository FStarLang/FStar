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
    let uu____392 = FStar_Unionfind.puf_empty ()  in
    let uu____395 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____392; univ_graph = uu____395; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____405 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____407 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____405 uu____407
  
let (state : uf FStar_ST.ref) =
  let uu____424 = let uu____425 = vops.next_major ()  in empty uu____425  in
  FStar_Util.mk_ref uu____424 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____451  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____501  ->
    let v1 = vops.next_major ()  in
    let uu____503 = empty v1  in set uu____503
  
let (new_transaction : unit -> tx) =
  fun uu____509  ->
    let tx = let uu____511 = get ()  in TX uu____511  in
    (let uu____513 =
       let uu___8_514 = get ()  in
       let uu____515 = vops.next_minor ()  in
       {
         term_graph = (uu___8_514.term_graph);
         univ_graph = (uu___8_514.univ_graph);
         version = uu____515
       }  in
     set uu____513);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____527  -> match uu____527 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____589  -> let uu____590 = get ()  in uu____590.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____596  -> let uu____597 = get ()  in uu____597.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____604 =
      let uu___9_605 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___9_605.univ_graph);
        version = (uu___9_605.version)
      }  in
    set uu____604
  
let chk_v :
  'Auu____611 . ('Auu____611 * FStar_Syntax_Syntax.version) -> 'Auu____611 =
  fun uu____620  ->
    match uu____620 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____632 =
             let uu____634 = version_to_string expected  in
             let uu____636 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____634 uu____636
              in
           failwith uu____632)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____646 = get_term_graph ()  in
    let uu____651 = chk_v u  in FStar_Unionfind.puf_id uu____646 uu____651
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____672 =
      let uu____679 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____679 n1  in
    let uu____686 = get_version ()  in (uu____672, uu____686)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____698  ->
    let uu____699 =
      let uu____706 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____706 FStar_Pervasives_Native.None  in
    let uu____713 = get_version ()  in (uu____699, uu____713)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____728 = get_term_graph ()  in
    let uu____733 = chk_v u  in FStar_Unionfind.puf_find uu____728 uu____733
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____757 =
        let uu____758 = get_term_graph ()  in
        let uu____763 = chk_v u  in
        FStar_Unionfind.puf_change uu____758 uu____763
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____757
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____788 = get_term_graph ()  in
      let uu____793 = chk_v u  in
      let uu____804 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____788 uu____793 uu____804
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____828 =
        let uu____829 = get_term_graph ()  in
        let uu____834 = chk_v u  in
        let uu____845 = chk_v v1  in
        FStar_Unionfind.puf_union uu____829 uu____834 uu____845  in
      set_term_graph uu____828
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____863  -> let uu____864 = get ()  in uu____864.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____871 =
      let uu___10_872 = get ()  in
      {
        term_graph = (uu___10_872.term_graph);
        univ_graph = ug;
        version = (uu___10_872.version)
      }  in
    set uu____871
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____880 = get_univ_graph ()  in
    let uu____885 = chk_v u  in FStar_Unionfind.puf_id uu____880 uu____885
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____904 =
      let uu____909 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____909 n1  in
    let uu____916 = get_version ()  in (uu____904, uu____916)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____926  ->
    let uu____927 =
      let uu____932 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____932 FStar_Pervasives_Native.None  in
    let uu____939 = get_version ()  in (uu____927, uu____939)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____952 = get_univ_graph ()  in
    let uu____957 = chk_v u  in FStar_Unionfind.puf_find uu____952 uu____957
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____979 =
        let uu____980 = get_univ_graph ()  in
        let uu____985 = chk_v u  in
        FStar_Unionfind.puf_change uu____980 uu____985
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____979
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____1008 = get_univ_graph ()  in
      let uu____1013 = chk_v u  in
      let uu____1022 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____1008 uu____1013 uu____1022
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____1044 =
        let uu____1045 = get_univ_graph ()  in
        let uu____1050 = chk_v u  in
        let uu____1059 = chk_v v1  in
        FStar_Unionfind.puf_union uu____1045 uu____1050 uu____1059  in
      set_univ_graph uu____1044
  