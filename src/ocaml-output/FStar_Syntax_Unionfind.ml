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
  let next_major uu____42062 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____42108 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____42108;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____42193 =
    let uu____42194 = FStar_ST.op_Bang major  in
    let uu____42239 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____42194;
      FStar_Syntax_Syntax.minor = uu____42239
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
    let uu____42374 = FStar_Unionfind.puf_empty ()  in
    let uu____42377 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____42374; univ_graph = uu____42377; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____42387 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____42389 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____42387 uu____42389
  
let (state : uf FStar_ST.ref) =
  let uu____42406 =
    let uu____42407 = vops.next_major ()  in empty uu____42407  in
  FStar_Util.mk_ref uu____42406 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____42433  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____42483  ->
    let v1 = vops.next_major ()  in
    let uu____42485 = empty v1  in set uu____42485
  
let (new_transaction : unit -> tx) =
  fun uu____42491  ->
    let tx = let uu____42493 = get ()  in TX uu____42493  in
    (let uu____42495 =
       let uu___425_42496 = get ()  in
       let uu____42497 = vops.next_minor ()  in
       {
         term_graph = (uu___425_42496.term_graph);
         univ_graph = (uu___425_42496.univ_graph);
         version = uu____42497
       }  in
     set uu____42495);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____42509  -> match uu____42509 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____42571  -> let uu____42572 = get ()  in uu____42572.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____42578  -> let uu____42579 = get ()  in uu____42579.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____42586 =
      let uu___438_42587 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_42587.univ_graph);
        version = (uu___438_42587.version)
      }  in
    set uu____42586
  
let chk_v :
  'Auu____42593 .
    ('Auu____42593 * FStar_Syntax_Syntax.version) -> 'Auu____42593
  =
  fun uu____42602  ->
    match uu____42602 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____42614 =
             let uu____42616 = version_to_string expected  in
             let uu____42618 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____42616 uu____42618
              in
           failwith uu____42614)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____42628 = get_term_graph ()  in
    let uu____42633 = chk_v u  in
    FStar_Unionfind.puf_id uu____42628 uu____42633
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____42654 =
      let uu____42661 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____42661 n1  in
    let uu____42668 = get_version ()  in (uu____42654, uu____42668)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____42680  ->
    let uu____42681 =
      let uu____42688 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____42688 FStar_Pervasives_Native.None  in
    let uu____42695 = get_version ()  in (uu____42681, uu____42695)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42710 = get_term_graph ()  in
    let uu____42715 = chk_v u  in
    FStar_Unionfind.puf_find uu____42710 uu____42715
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____42739 =
        let uu____42740 = get_term_graph ()  in
        let uu____42745 = chk_v u  in
        FStar_Unionfind.puf_change uu____42740 uu____42745
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____42739
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____42770 = get_term_graph ()  in
      let uu____42775 = chk_v u  in
      let uu____42786 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42770 uu____42775 uu____42786
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____42810 =
        let uu____42811 = get_term_graph ()  in
        let uu____42816 = chk_v u  in
        let uu____42827 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42811 uu____42816 uu____42827  in
      set_term_graph uu____42810
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____42845  -> let uu____42846 = get ()  in uu____42846.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____42853 =
      let uu___457_42854 = get ()  in
      {
        term_graph = (uu___457_42854.term_graph);
        univ_graph = ug;
        version = (uu___457_42854.version)
      }  in
    set uu____42853
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____42862 = get_univ_graph ()  in
    let uu____42867 = chk_v u  in
    FStar_Unionfind.puf_id uu____42862 uu____42867
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____42886 =
      let uu____42891 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____42891 n1  in
    let uu____42898 = get_version ()  in (uu____42886, uu____42898)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____42908  ->
    let uu____42909 =
      let uu____42914 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____42914 FStar_Pervasives_Native.None  in
    let uu____42921 = get_version ()  in (uu____42909, uu____42921)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42934 = get_univ_graph ()  in
    let uu____42939 = chk_v u  in
    FStar_Unionfind.puf_find uu____42934 uu____42939
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____42961 =
        let uu____42962 = get_univ_graph ()  in
        let uu____42967 = chk_v u  in
        FStar_Unionfind.puf_change uu____42962 uu____42967
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____42961
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____42990 = get_univ_graph ()  in
      let uu____42995 = chk_v u  in
      let uu____43004 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42990 uu____42995 uu____43004
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____43026 =
        let uu____43027 = get_univ_graph ()  in
        let uu____43032 = chk_v u  in
        let uu____43041 = chk_v v1  in
        FStar_Unionfind.puf_union uu____43027 uu____43032 uu____43041  in
      set_univ_graph uu____43026
  