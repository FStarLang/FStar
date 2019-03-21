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
  let next_major uu____37633 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____37657 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____37657;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____37687 =
    let uu____37688 = FStar_ST.op_Bang major  in
    let uu____37711 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____37688;
      FStar_Syntax_Syntax.minor = uu____37711
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
    let uu____37791 = FStar_Unionfind.puf_empty ()  in
    let uu____37794 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____37791; univ_graph = uu____37794; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____37804 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____37806 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____37804 uu____37806
  
let (state : uf FStar_ST.ref) =
  let uu____37812 =
    let uu____37813 = vops.next_major ()  in empty uu____37813  in
  FStar_Util.mk_ref uu____37812 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____37839  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____37889  ->
    let v1 = vops.next_major ()  in
    let uu____37891 = empty v1  in set uu____37891
  
let (new_transaction : unit -> tx) =
  fun uu____37897  ->
    let tx = let uu____37899 = get ()  in TX uu____37899  in
    (let uu____37901 =
       let uu___425_37902 = get ()  in
       let uu____37903 = vops.next_minor ()  in
       {
         term_graph = (uu___425_37902.term_graph);
         univ_graph = (uu___425_37902.univ_graph);
         version = uu____37903
       }  in
     set uu____37901);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____37915  -> match uu____37915 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____37944  -> let uu____37945 = get ()  in uu____37945.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____37951  -> let uu____37952 = get ()  in uu____37952.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____37959 =
      let uu___438_37960 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_37960.univ_graph);
        version = (uu___438_37960.version)
      }  in
    set uu____37959
  
let chk_v :
  'Auu____37966 .
    ('Auu____37966 * FStar_Syntax_Syntax.version) -> 'Auu____37966
  =
  fun uu____37975  ->
    match uu____37975 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____37987 =
             let uu____37989 = version_to_string expected  in
             let uu____37991 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____37989 uu____37991
              in
           failwith uu____37987)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____38001 = get_term_graph ()  in
    let uu____38006 = chk_v u  in
    FStar_Unionfind.puf_id uu____38001 uu____38006
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____38027 =
      let uu____38034 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____38034 n1  in
    let uu____38041 = get_version ()  in (uu____38027, uu____38041)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____38053  ->
    let uu____38054 =
      let uu____38061 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____38061 FStar_Pervasives_Native.None  in
    let uu____38068 = get_version ()  in (uu____38054, uu____38068)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____38083 = get_term_graph ()  in
    let uu____38088 = chk_v u  in
    FStar_Unionfind.puf_find uu____38083 uu____38088
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____38112 =
        let uu____38113 = get_term_graph ()  in
        let uu____38118 = chk_v u  in
        FStar_Unionfind.puf_change uu____38113 uu____38118
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____38112
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____38143 = get_term_graph ()  in
      let uu____38148 = chk_v u  in
      let uu____38159 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____38143 uu____38148 uu____38159
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____38183 =
        let uu____38184 = get_term_graph ()  in
        let uu____38189 = chk_v u  in
        let uu____38200 = chk_v v1  in
        FStar_Unionfind.puf_union uu____38184 uu____38189 uu____38200  in
      set_term_graph uu____38183
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____38218  -> let uu____38219 = get ()  in uu____38219.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____38226 =
      let uu___457_38227 = get ()  in
      {
        term_graph = (uu___457_38227.term_graph);
        univ_graph = ug;
        version = (uu___457_38227.version)
      }  in
    set uu____38226
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____38235 = get_univ_graph ()  in
    let uu____38240 = chk_v u  in
    FStar_Unionfind.puf_id uu____38235 uu____38240
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____38259 =
      let uu____38264 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____38264 n1  in
    let uu____38271 = get_version ()  in (uu____38259, uu____38271)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____38281  ->
    let uu____38282 =
      let uu____38287 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____38287 FStar_Pervasives_Native.None  in
    let uu____38294 = get_version ()  in (uu____38282, uu____38294)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____38307 = get_univ_graph ()  in
    let uu____38312 = chk_v u  in
    FStar_Unionfind.puf_find uu____38307 uu____38312
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____38334 =
        let uu____38335 = get_univ_graph ()  in
        let uu____38340 = chk_v u  in
        FStar_Unionfind.puf_change uu____38335 uu____38340
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____38334
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____38363 = get_univ_graph ()  in
      let uu____38368 = chk_v u  in
      let uu____38377 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____38363 uu____38368 uu____38377
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____38399 =
        let uu____38400 = get_univ_graph ()  in
        let uu____38405 = chk_v u  in
        let uu____38414 = chk_v v1  in
        FStar_Unionfind.puf_union uu____38400 uu____38405 uu____38414  in
      set_univ_graph uu____38399
  