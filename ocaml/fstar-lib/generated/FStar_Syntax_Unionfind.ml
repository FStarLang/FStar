open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with | { next_major; next_minor;_} -> next_major
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with | { next_major; next_minor;_} -> next_minor
let (vops : vops_t) =
  let major = FStar_Compiler_Util.mk_ref Prims.int_zero in
  let minor = FStar_Compiler_Util.mk_ref Prims.int_zero in
  let next_major uu___ =
    FStar_Compiler_Effect.op_Colon_Equals minor Prims.int_zero;
    (let uu___2 =
       FStar_Compiler_Util.incr major; FStar_Compiler_Effect.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu___2;
       FStar_Syntax_Syntax.minor = Prims.int_zero
     }) in
  let next_minor uu___ =
    let uu___1 = FStar_Compiler_Effect.op_Bang major in
    let uu___2 =
      FStar_Compiler_Util.incr minor; FStar_Compiler_Effect.op_Bang minor in
    { FStar_Syntax_Syntax.major = uu___1; FStar_Syntax_Syntax.minor = uu___2
    } in
  { next_major; next_minor }
type tgraph =
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.uvar_decoration) FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version ;
  ro: Prims.bool }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> term_graph
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> univ_graph
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> version
let (__proj__Mkuf__item__ro : uf -> Prims.bool) =
  fun projectee ->
    match projectee with | { term_graph; univ_graph; version; ro;_} -> ro
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v ->
    let uu___ = FStar_Unionfind.puf_empty () in
    let uu___1 = FStar_Unionfind.puf_empty () in
    { term_graph = uu___; univ_graph = uu___1; version = v; ro = false }
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu___ = FStar_Compiler_Util.string_of_int v.FStar_Syntax_Syntax.major in
    let uu___1 =
      FStar_Compiler_Util.string_of_int v.FStar_Syntax_Syntax.minor in
    FStar_Compiler_Util.format2 "%s.%s" uu___ uu___1
let (state : uf FStar_Compiler_Effect.ref) =
  let uu___ = let uu___1 = vops.next_major () in empty uu___1 in
  FStar_Compiler_Util.mk_ref uu___
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee -> true
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee -> match projectee with | TX _0 -> _0
let (get : unit -> uf) = fun uu___ -> FStar_Compiler_Effect.op_Bang state
let (set_ro : unit -> unit) =
  fun uu___ ->
    let s = get () in
    FStar_Compiler_Effect.op_Colon_Equals state
      {
        term_graph = (s.term_graph);
        univ_graph = (s.univ_graph);
        version = (s.version);
        ro = true
      }
let (set_rw : unit -> unit) =
  fun uu___ ->
    let s = get () in
    FStar_Compiler_Effect.op_Colon_Equals state
      {
        term_graph = (s.term_graph);
        univ_graph = (s.univ_graph);
        version = (s.version);
        ro = false
      }
let with_uf_enabled : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let s = get () in
    set_rw ();
    (let restore uu___1 = if s.ro then set_ro () else () in
     let r =
       let uu___1 = FStar_Options.trace_error () in
       if uu___1
       then f ()
       else
         (try (fun uu___3 -> match () with | () -> f ()) ()
          with | uu___3 -> (restore (); FStar_Compiler_Effect.raise uu___3)) in
     restore (); r)
let (fail_if_ro : unit -> unit) =
  fun uu___ ->
    let uu___1 = let uu___2 = get () in uu___2.ro in
    if uu___1
    then
      FStar_Errors.raise_error
        (FStar_Errors.Fatal_BadUvar,
          "Internal error: UF graph was in read-only mode")
        FStar_Compiler_Range.dummyRange
    else ()
let (set : uf -> unit) =
  fun u -> fail_if_ro (); FStar_Compiler_Effect.op_Colon_Equals state u
let (reset : unit -> unit) =
  fun uu___ ->
    fail_if_ro ();
    (let v = vops.next_major () in
     let uu___2 =
       let uu___3 = empty v in
       {
         term_graph = (uu___3.term_graph);
         univ_graph = (uu___3.univ_graph);
         version = (uu___3.version);
         ro = false
       } in
     set uu___2)
let (new_transaction : unit -> tx) =
  fun uu___ ->
    let tx1 = let uu___1 = get () in TX uu___1 in
    (let uu___2 =
       let uu___3 = get () in
       let uu___4 = vops.next_minor () in
       {
         term_graph = (uu___3.term_graph);
         univ_graph = (uu___3.univ_graph);
         version = uu___4;
         ro = (uu___3.ro)
       } in
     set uu___2);
    tx1
let (commit : tx -> unit) = fun tx1 -> ()
let (rollback : tx -> unit) =
  fun uu___ -> match uu___ with | TX uf1 -> set uf1
let update_in_tx : 'a . 'a FStar_Compiler_Effect.ref -> 'a -> unit =
  fun r -> fun x -> ()
let (get_term_graph : unit -> tgraph) =
  fun uu___ -> let uu___1 = get () in uu___1.term_graph
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu___ -> let uu___1 = get () in uu___1.version
let (set_term_graph : tgraph -> unit) =
  fun tg ->
    let uu___ =
      let uu___1 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___1.univ_graph);
        version = (uu___1.version);
        ro = (uu___1.ro)
      } in
    set uu___
let (chk_v_t :
  FStar_Syntax_Syntax.uvar ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.uvar_decoration)
      FStar_Unionfind.p_uvar)
  =
  fun su ->
    let uu___ = su in
    match uu___ with
    | (u, v, rng) ->
        let uvar_to_string u1 =
          let uu___1 =
            let uu___2 =
              let uu___3 = get_term_graph () in
              FStar_Unionfind.puf_id uu___3 u1 in
            FStar_Compiler_Effect.op_Bar_Greater uu___2
              FStar_Compiler_Util.string_of_int in
          Prims.op_Hat "?" uu___1 in
        let expected = get_version () in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = uvar_to_string u in
               let uu___5 = version_to_string expected in
               let uu___6 = version_to_string v in
               FStar_Compiler_Util.format3
                 "Internal error: incompatible version for term unification variable %s: current version is %s; got version %s"
                 uu___4 uu___5 uu___6 in
             (FStar_Errors.Fatal_BadUvar, uu___3) in
           FStar_Errors.raise_error uu___2 rng)
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u ->
    let uu___ = get_term_graph () in
    let uu___1 = chk_v_t u in FStar_Unionfind.puf_id uu___ uu___1
let (fresh :
  FStar_Syntax_Syntax.uvar_decoration ->
    FStar_Compiler_Range.range -> FStar_Syntax_Syntax.uvar)
  =
  fun decoration ->
    fun rng ->
      fail_if_ro ();
      (let uu___1 =
         let uu___2 = get_term_graph () in
         FStar_Unionfind.puf_fresh uu___2
           (FStar_Pervasives_Native.None, decoration) in
       let uu___2 = get_version () in (uu___1, uu___2, rng))
let (find_core :
  FStar_Syntax_Syntax.uvar ->
    (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.uvar_decoration))
  =
  fun u ->
    let uu___ = get_term_graph () in
    let uu___1 = chk_v_t u in FStar_Unionfind.puf_find uu___ uu___1
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun u -> let uu___ = find_core u in FStar_Pervasives_Native.fst uu___
let (find_decoration :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar_decoration) =
  fun u -> let uu___ = find_core u in FStar_Pervasives_Native.snd uu___
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u ->
    fun t ->
      let uu___ = find_core u in
      match uu___ with
      | (uu___1, dec) ->
          let uu___2 =
            let uu___3 = get_term_graph () in
            let uu___4 = chk_v_t u in
            FStar_Unionfind.puf_change uu___3 uu___4
              ((FStar_Pervasives_Native.Some t), dec) in
          set_term_graph uu___2
let (change_decoration :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar_decoration -> unit) =
  fun u ->
    fun d ->
      let uu___ = find_core u in
      match uu___ with
      | (t, uu___1) ->
          let uu___2 =
            let uu___3 = get_term_graph () in
            let uu___4 = chk_v_t u in
            FStar_Unionfind.puf_change uu___3 uu___4 (t, d) in
          set_term_graph uu___2
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u ->
    fun v ->
      let uu___ = get_term_graph () in
      let uu___1 = chk_v_t u in
      let uu___2 = chk_v_t v in
      FStar_Unionfind.puf_equivalent uu___ uu___1 uu___2
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u ->
    fun v ->
      let uu___ =
        let uu___1 = get_term_graph () in
        let uu___2 = chk_v_t u in
        let uu___3 = chk_v_t v in
        FStar_Unionfind.puf_union uu___1 uu___2 uu___3 in
      set_term_graph uu___
let (get_univ_graph : unit -> ugraph) =
  fun uu___ -> let uu___1 = get () in uu___1.univ_graph
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version *
    FStar_Compiler_Range.range) ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu___ ->
    match uu___ with
    | (u, v, rng) ->
        let uvar_to_string u1 =
          let uu___1 =
            let uu___2 =
              let uu___3 = get_univ_graph () in
              FStar_Unionfind.puf_id uu___3 u1 in
            FStar_Compiler_Effect.op_Bar_Greater uu___2
              FStar_Compiler_Util.string_of_int in
          Prims.op_Hat "?" uu___1 in
        let expected = get_version () in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = uvar_to_string u in
               let uu___5 = version_to_string expected in
               let uu___6 = version_to_string v in
               FStar_Compiler_Util.format3
                 "Internal error: incompatible version for universe unification variable %s: current version is %s; got version %s"
                 uu___4 uu___5 uu___6 in
             (FStar_Errors.Fatal_BadUvar, uu___3) in
           FStar_Errors.raise_error uu___2 rng)
let (set_univ_graph : ugraph -> unit) =
  fun ug ->
    let uu___ =
      let uu___1 = get () in
      {
        term_graph = (uu___1.term_graph);
        univ_graph = ug;
        version = (uu___1.version);
        ro = (uu___1.ro)
      } in
    set uu___
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u ->
    let uu___ = get_univ_graph () in
    let uu___1 = chk_v_u u in FStar_Unionfind.puf_id uu___ uu___1
let (univ_fresh :
  FStar_Compiler_Range.range -> FStar_Syntax_Syntax.universe_uvar) =
  fun rng ->
    fail_if_ro ();
    (let uu___1 =
       let uu___2 = get_univ_graph () in
       FStar_Unionfind.puf_fresh uu___2 FStar_Pervasives_Native.None in
     let uu___2 = get_version () in (uu___1, uu___2, rng))
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    let uu___ = get_univ_graph () in
    let uu___1 = chk_v_u u in FStar_Unionfind.puf_find uu___ uu___1
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u ->
    fun t ->
      let uu___ =
        let uu___1 = get_univ_graph () in
        let uu___2 = chk_v_u u in
        FStar_Unionfind.puf_change uu___1 uu___2
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu___
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u ->
    fun v ->
      let uu___ = get_univ_graph () in
      let uu___1 = chk_v_u u in
      let uu___2 = chk_v_u v in
      FStar_Unionfind.puf_equivalent uu___ uu___1 uu___2
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u ->
    fun v ->
      let uu___ =
        let uu___1 = get_univ_graph () in
        let uu___2 = chk_v_u u in
        let uu___3 = chk_v_u v in
        FStar_Unionfind.puf_union uu___1 uu___2 uu___3 in
      set_univ_graph uu___