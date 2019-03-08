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
  let next_major uu____37618 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____37642 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____37642;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____37672 =
    let uu____37673 = FStar_ST.op_Bang major  in
    let uu____37696 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____37673;
      FStar_Syntax_Syntax.minor = uu____37696
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
    let uu____37776 = FStar_Unionfind.puf_empty ()  in
    let uu____37779 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____37776; univ_graph = uu____37779; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____37789 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____37791 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____37789 uu____37791
  
let (state : uf FStar_ST.ref) =
  let uu____37797 =
    let uu____37798 = vops.next_major ()  in empty uu____37798  in
  FStar_Util.mk_ref uu____37797 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____37824  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____37874  ->
    let v1 = vops.next_major ()  in
    let uu____37876 = empty v1  in set uu____37876
  
let (new_transaction : unit -> tx) =
  fun uu____37882  ->
    let tx = let uu____37884 = get ()  in TX uu____37884  in
    (let uu____37886 =
       let uu___425_37887 = get ()  in
       let uu____37888 = vops.next_minor ()  in
       {
         term_graph = (uu___425_37887.term_graph);
         univ_graph = (uu___425_37887.univ_graph);
         version = uu____37888
       }  in
     set uu____37886);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____37900  -> match uu____37900 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____37929  -> let uu____37930 = get ()  in uu____37930.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____37936  -> let uu____37937 = get ()  in uu____37937.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____37944 =
      let uu___438_37945 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_37945.univ_graph);
        version = (uu___438_37945.version)
      }  in
    set uu____37944
  
let chk_v :
  'Auu____37951 .
    ('Auu____37951 * FStar_Syntax_Syntax.version) -> 'Auu____37951
  =
  fun uu____37960  ->
    match uu____37960 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____37972 =
             let uu____37974 = version_to_string expected  in
             let uu____37976 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____37974 uu____37976
              in
           failwith uu____37972)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____37986 = get_term_graph ()  in
    let uu____37991 = chk_v u  in
    FStar_Unionfind.puf_id uu____37986 uu____37991
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____38012 =
      let uu____38019 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____38019 n1  in
    let uu____38026 = get_version ()  in (uu____38012, uu____38026)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____38038  ->
    let uu____38039 =
      let uu____38046 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____38046 FStar_Pervasives_Native.None  in
    let uu____38053 = get_version ()  in (uu____38039, uu____38053)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____38068 = get_term_graph ()  in
    let uu____38073 = chk_v u  in
    FStar_Unionfind.puf_find uu____38068 uu____38073
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____38097 =
        let uu____38098 = get_term_graph ()  in
        let uu____38103 = chk_v u  in
        FStar_Unionfind.puf_change uu____38098 uu____38103
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____38097
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____38128 = get_term_graph ()  in
      let uu____38133 = chk_v u  in
      let uu____38144 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____38128 uu____38133 uu____38144
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____38168 =
        let uu____38169 = get_term_graph ()  in
        let uu____38174 = chk_v u  in
        let uu____38185 = chk_v v1  in
        FStar_Unionfind.puf_union uu____38169 uu____38174 uu____38185  in
      set_term_graph uu____38168
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____38203  -> let uu____38204 = get ()  in uu____38204.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____38211 =
      let uu___457_38212 = get ()  in
      {
        term_graph = (uu___457_38212.term_graph);
        univ_graph = ug;
        version = (uu___457_38212.version)
      }  in
    set uu____38211
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____38220 = get_univ_graph ()  in
    let uu____38225 = chk_v u  in
    FStar_Unionfind.puf_id uu____38220 uu____38225
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____38244 =
      let uu____38249 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____38249 n1  in
    let uu____38256 = get_version ()  in (uu____38244, uu____38256)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____38266  ->
    let uu____38267 =
      let uu____38272 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____38272 FStar_Pervasives_Native.None  in
    let uu____38279 = get_version ()  in (uu____38267, uu____38279)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____38292 = get_univ_graph ()  in
    let uu____38297 = chk_v u  in
    FStar_Unionfind.puf_find uu____38292 uu____38297
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____38319 =
        let uu____38320 = get_univ_graph ()  in
        let uu____38325 = chk_v u  in
        FStar_Unionfind.puf_change uu____38320 uu____38325
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____38319
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____38348 = get_univ_graph ()  in
      let uu____38353 = chk_v u  in
      let uu____38362 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____38348 uu____38353 uu____38362
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____38384 =
        let uu____38385 = get_univ_graph ()  in
        let uu____38390 = chk_v u  in
        let uu____38399 = chk_v v1  in
        FStar_Unionfind.puf_union uu____38385 uu____38390 uu____38399  in
      set_univ_graph uu____38384
  