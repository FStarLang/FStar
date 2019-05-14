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
  let next_major uu____134 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____158 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____158;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____190 =
    let uu____191 = FStar_ST.op_Bang major  in
    let uu____214 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____191;
      FStar_Syntax_Syntax.minor = uu____214
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
    let uu____348 = FStar_Unionfind.puf_empty ()  in
    let uu____355 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____348; univ_graph = uu____355; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____369 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____371 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____369 uu____371
  
let (state : uf FStar_ST.ref) =
  let uu____380 = let uu____387 = vops.next_major ()  in empty uu____387  in
  FStar_Util.mk_ref uu____380 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____469  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____537  ->
    let v1 = vops.next_major ()  in
    let uu____543 = empty v1  in set uu____543
  
let (new_transaction : unit -> tx) =
  fun uu____559  ->
    let tx = let uu____569 = get ()  in TX uu____569  in
    (let uu____577 =
       let uu___34_584 = get ()  in
       let uu____591 = vops.next_minor ()  in
       {
         term_graph = (uu___34_584.term_graph);
         univ_graph = (uu___34_584.univ_graph);
         version = uu____591
       }  in
     set uu____577);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____619  -> match uu____619 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____655  -> let uu____656 = get ()  in uu____656.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____670  -> let uu____671 = get ()  in uu____671.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____684 =
      let uu___47_691 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___47_691.univ_graph);
        version = (uu___47_691.version)
      }  in
    set uu____684
  
let chk_v :
  'Auu____703 . ('Auu____703 * FStar_Syntax_Syntax.version) -> 'Auu____703 =
  fun uu____714  ->
    match uu____714 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____736 =
             let uu____738 = version_to_string expected  in
             let uu____740 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____738 uu____740
              in
           failwith uu____736)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____750 = get_term_graph ()  in
    let uu____759 = chk_v u  in FStar_Unionfind.puf_id uu____750 uu____759
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____792 =
      let uu____803 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____803 n1  in
    let uu____818 = get_version ()  in (uu____792, uu____818)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____840  ->
    let uu____841 =
      let uu____852 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____852 FStar_Pervasives_Native.None  in
    let uu____871 = get_version ()  in (uu____841, uu____871)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____900 = get_term_graph ()  in
    let uu____909 = chk_v u  in FStar_Unionfind.puf_find uu____900 uu____909
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____953 =
        let uu____954 = get_term_graph ()  in
        let uu____963 = chk_v u  in
        FStar_Unionfind.puf_change uu____954 uu____963
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____953
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____1004 = get_term_graph ()  in
      let uu____1013 = chk_v u  in
      let uu____1032 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____1004 uu____1013 uu____1032
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____1068 =
        let uu____1069 = get_term_graph ()  in
        let uu____1078 = chk_v u  in
        let uu____1097 = chk_v v1  in
        FStar_Unionfind.puf_union uu____1069 uu____1078 uu____1097  in
      set_term_graph uu____1068
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____1127  -> let uu____1128 = get ()  in uu____1128.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____1141 =
      let uu___66_1148 = get ()  in
      {
        term_graph = (uu___66_1148.term_graph);
        univ_graph = ug;
        version = (uu___66_1148.version)
      }  in
    set uu____1141
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____1162 = get_univ_graph ()  in
    let uu____1167 = chk_v u  in FStar_Unionfind.puf_id uu____1162 uu____1167
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____1186 =
      let uu____1191 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____1191 n1  in
    let uu____1198 = get_version ()  in (uu____1186, uu____1198)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____1214  ->
    let uu____1215 =
      let uu____1220 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____1220 FStar_Pervasives_Native.None  in
    let uu____1227 = get_version ()  in (uu____1215, uu____1227)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____1246 = get_univ_graph ()  in
    let uu____1251 = chk_v u  in
    FStar_Unionfind.puf_find uu____1246 uu____1251
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____1273 =
        let uu____1274 = get_univ_graph ()  in
        let uu____1279 = chk_v u  in
        FStar_Unionfind.puf_change uu____1274 uu____1279
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____1273
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____1302 = get_univ_graph ()  in
      let uu____1307 = chk_v u  in
      let uu____1316 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____1302 uu____1307 uu____1316
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____1338 =
        let uu____1339 = get_univ_graph ()  in
        let uu____1344 = chk_v u  in
        let uu____1353 = chk_v v1  in
        FStar_Unionfind.puf_union uu____1339 uu____1344 uu____1353  in
      set_univ_graph uu____1338
  