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
  let major = FStar_Util.mk_ref Prims.int_zero  in
  let minor = FStar_Util.mk_ref Prims.int_zero  in
  let next_major uu____85 =
    FStar_ST.op_Colon_Equals minor Prims.int_zero;
    (let uu____109 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____109;
       FStar_Syntax_Syntax.minor = Prims.int_zero
     })
     in
  let next_minor uu____139 =
    let uu____140 = FStar_ST.op_Bang major  in
    let uu____163 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____140;
      FStar_Syntax_Syntax.minor = uu____163
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
    let uu____243 = FStar_Unionfind.puf_empty ()  in
    let uu____246 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____243; univ_graph = uu____246; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____256 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____258 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____256 uu____258
  
let (state : uf FStar_ST.ref) =
  let uu____264 = let uu____265 = vops.next_major ()  in empty uu____265  in
  FStar_Util.mk_ref uu____264 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____291  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____341  ->
    let v1 = vops.next_major ()  in
    let uu____343 = empty v1  in set uu____343
  
let (new_transaction : unit -> tx) =
  fun uu____349  ->
    let tx = let uu____351 = get ()  in TX uu____351  in
    (let uu____353 =
       let uu___34_354 = get ()  in
       let uu____355 = vops.next_minor ()  in
       {
         term_graph = (uu___34_354.term_graph);
         univ_graph = (uu___34_354.univ_graph);
         version = uu____355
       }  in
     set uu____353);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____367  -> match uu____367 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____396  -> let uu____397 = get ()  in uu____397.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____403  -> let uu____404 = get ()  in uu____404.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____411 =
      let uu___47_412 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___47_412.univ_graph);
        version = (uu___47_412.version)
      }  in
    set uu____411
  
let (chk_v_t :
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____430  ->
    match uu____430 with
    | (u,v1) ->
        let uvar_to_string u1 =
          let uu____468 =
            let uu____470 =
              let uu____472 = get_term_graph ()  in
              FStar_Unionfind.puf_id uu____472 u1  in
            FStar_All.pipe_right uu____470 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____468  in
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____491 =
             let uu____493 = uvar_to_string u  in
             let uu____495 = version_to_string expected  in
             let uu____497 = version_to_string v1  in
             FStar_Util.format3
               "Incompatible version for term unification variable %s: current version is %s; got version %s"
               uu____493 uu____495 uu____497
              in
           failwith uu____491)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____511 = get_term_graph ()  in
    let uu____516 = chk_v_t u  in FStar_Unionfind.puf_id uu____511 uu____516
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____531 =
      let uu____538 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____538 n1  in
    let uu____545 = get_version ()  in (uu____531, uu____545)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____557  ->
    let uu____558 =
      let uu____565 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____565 FStar_Pervasives_Native.None  in
    let uu____572 = get_version ()  in (uu____558, uu____572)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____587 = get_term_graph ()  in
    let uu____592 = chk_v_t u  in
    FStar_Unionfind.puf_find uu____587 uu____592
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____610 =
        let uu____611 = get_term_graph ()  in
        let uu____616 = chk_v_t u  in
        FStar_Unionfind.puf_change uu____611 uu____616
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____610
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____635 = get_term_graph ()  in
      let uu____640 = chk_v_t u  in
      let uu____645 = chk_v_t v1  in
      FStar_Unionfind.puf_equivalent uu____635 uu____640 uu____645
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____663 =
        let uu____664 = get_term_graph ()  in
        let uu____669 = chk_v_t u  in
        let uu____674 = chk_v_t v1  in
        FStar_Unionfind.puf_union uu____664 uu____669 uu____674  in
      set_term_graph uu____663
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____686  -> let uu____687 = get ()  in uu____687.univ_graph 
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____705  ->
    match uu____705 with
    | (u,v1) ->
        let uvar_to_string u1 =
          let uu____743 =
            let uu____745 =
              let uu____747 = get_univ_graph ()  in
              FStar_Unionfind.puf_id uu____747 u1  in
            FStar_All.pipe_right uu____745 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____743  in
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____766 =
             let uu____768 = uvar_to_string u  in
             let uu____770 = version_to_string expected  in
             let uu____772 = version_to_string v1  in
             FStar_Util.format3
               "Incompatible version for universe unification variable %s: current version is %s; got version %s"
               uu____768 uu____770 uu____772
              in
           failwith uu____766)
  
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____785 =
      let uu___75_786 = get ()  in
      {
        term_graph = (uu___75_786.term_graph);
        univ_graph = ug;
        version = (uu___75_786.version)
      }  in
    set uu____785
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____794 = get_univ_graph ()  in
    let uu____799 = chk_v_u u  in FStar_Unionfind.puf_id uu____794 uu____799
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____814 =
      let uu____819 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____819 n1  in
    let uu____826 = get_version ()  in (uu____814, uu____826)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____836  ->
    let uu____837 =
      let uu____842 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____842 FStar_Pervasives_Native.None  in
    let uu____849 = get_version ()  in (uu____837, uu____849)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____862 = get_univ_graph ()  in
    let uu____867 = chk_v_u u  in
    FStar_Unionfind.puf_find uu____862 uu____867
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____885 =
        let uu____886 = get_univ_graph ()  in
        let uu____891 = chk_v_u u  in
        FStar_Unionfind.puf_change uu____886 uu____891
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____885
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____910 = get_univ_graph ()  in
      let uu____915 = chk_v_u u  in
      let uu____920 = chk_v_u v1  in
      FStar_Unionfind.puf_equivalent uu____910 uu____915 uu____920
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____938 =
        let uu____939 = get_univ_graph ()  in
        let uu____944 = chk_v_u u  in
        let uu____949 = chk_v_u v1  in
        FStar_Unionfind.puf_union uu____939 uu____944 uu____949  in
      set_univ_graph uu____938
  