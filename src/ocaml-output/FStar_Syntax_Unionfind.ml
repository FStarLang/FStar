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
  let next_major uu____38214 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____38238 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____38238;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____38268 =
    let uu____38269 = FStar_ST.op_Bang major  in
    let uu____38292 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____38269;
      FStar_Syntax_Syntax.minor = uu____38292
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
    let uu____38372 = FStar_Unionfind.puf_empty ()  in
    let uu____38375 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____38372; univ_graph = uu____38375; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____38385 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____38387 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____38385 uu____38387
  
let (state : uf FStar_ST.ref) =
  let uu____38393 =
    let uu____38394 = vops.next_major ()  in empty uu____38394  in
  FStar_Util.mk_ref uu____38393 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____38420  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____38470  ->
    let v1 = vops.next_major ()  in
    let uu____38472 = empty v1  in set uu____38472
  
let (new_transaction : unit -> tx) =
  fun uu____38478  ->
    let tx = let uu____38480 = get ()  in TX uu____38480  in
    (let uu____38482 =
       let uu___425_38483 = get ()  in
       let uu____38484 = vops.next_minor ()  in
       {
         term_graph = (uu___425_38483.term_graph);
         univ_graph = (uu___425_38483.univ_graph);
         version = uu____38484
       }  in
     set uu____38482);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____38496  -> match uu____38496 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____38525  -> let uu____38526 = get ()  in uu____38526.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____38532  -> let uu____38533 = get ()  in uu____38533.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____38540 =
      let uu___438_38541 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_38541.univ_graph);
        version = (uu___438_38541.version)
      }  in
    set uu____38540
  
let chk_v :
  'Auu____38547 .
    ('Auu____38547 * FStar_Syntax_Syntax.version) -> 'Auu____38547
  =
  fun uu____38556  ->
    match uu____38556 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____38568 =
             let uu____38570 = version_to_string expected  in
             let uu____38572 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____38570 uu____38572
              in
           failwith uu____38568)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____38582 = get_term_graph ()  in
    let uu____38587 = chk_v u  in
    FStar_Unionfind.puf_id uu____38582 uu____38587
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____38608 =
      let uu____38615 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____38615 n1  in
    let uu____38622 = get_version ()  in (uu____38608, uu____38622)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____38634  ->
    let uu____38635 =
      let uu____38642 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____38642 FStar_Pervasives_Native.None  in
    let uu____38649 = get_version ()  in (uu____38635, uu____38649)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____38664 = get_term_graph ()  in
    let uu____38669 = chk_v u  in
    FStar_Unionfind.puf_find uu____38664 uu____38669
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____38693 =
        let uu____38694 = get_term_graph ()  in
        let uu____38699 = chk_v u  in
        FStar_Unionfind.puf_change uu____38694 uu____38699
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____38693
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____38724 = get_term_graph ()  in
      let uu____38729 = chk_v u  in
      let uu____38740 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____38724 uu____38729 uu____38740
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____38764 =
        let uu____38765 = get_term_graph ()  in
        let uu____38770 = chk_v u  in
        let uu____38781 = chk_v v1  in
        FStar_Unionfind.puf_union uu____38765 uu____38770 uu____38781  in
      set_term_graph uu____38764
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____38799  -> let uu____38800 = get ()  in uu____38800.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____38807 =
      let uu___457_38808 = get ()  in
      {
        term_graph = (uu___457_38808.term_graph);
        univ_graph = ug;
        version = (uu___457_38808.version)
      }  in
    set uu____38807
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____38816 = get_univ_graph ()  in
    let uu____38821 = chk_v u  in
    FStar_Unionfind.puf_id uu____38816 uu____38821
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____38840 =
      let uu____38845 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____38845 n1  in
    let uu____38852 = get_version ()  in (uu____38840, uu____38852)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____38862  ->
    let uu____38863 =
      let uu____38868 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____38868 FStar_Pervasives_Native.None  in
    let uu____38875 = get_version ()  in (uu____38863, uu____38875)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____38888 = get_univ_graph ()  in
    let uu____38893 = chk_v u  in
    FStar_Unionfind.puf_find uu____38888 uu____38893
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____38915 =
        let uu____38916 = get_univ_graph ()  in
        let uu____38921 = chk_v u  in
        FStar_Unionfind.puf_change uu____38916 uu____38921
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____38915
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____38944 = get_univ_graph ()  in
      let uu____38949 = chk_v u  in
      let uu____38958 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____38944 uu____38949 uu____38958
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____38980 =
        let uu____38981 = get_univ_graph ()  in
        let uu____38986 = chk_v u  in
        let uu____38995 = chk_v v1  in
        FStar_Unionfind.puf_union uu____38981 uu____38986 uu____38995  in
      set_univ_graph uu____38980
  