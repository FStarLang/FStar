open Prims
let (is_in : unit -> FStar_Monotonic_HyperHeap.hmap -> Prims.bool) =
  fun r -> fun h -> FStar_Map.contains h ()
let (is_heap_color : Prims.int -> Prims.bool) = fun c -> c <= Prims.int_zero
type sid = unit
type 'm map_invariant_predicate = unit
type 'h downward_closed_predicate = unit
type ('tip, 'h) tip_top_predicate = unit
type ('h, 'n) rid_ctr_pred_predicate = unit
type 'm map_invariant = unit
type 'h downward_closed = unit
type ('tip, 'h) tip_top = unit
type ('h, 'n) rid_ctr_pred = unit
type ('tip, 'h) is_tip = unit
type ('h, 'ctr, 'tip) is_wf_with_ctr_and_tip = unit
type mem' =
  | HS of Prims.int * FStar_Monotonic_HyperHeap.hmap * unit 
let (uu___is_HS : mem' -> Prims.bool) = fun projectee -> true
let (__proj__HS__item__rid_ctr : mem' -> Prims.int) =
  fun projectee -> match projectee with | HS (rid_ctr, h, tip) -> rid_ctr
let (__proj__HS__item__h : mem' -> FStar_Monotonic_HyperHeap.hmap) =
  fun projectee -> match projectee with | HS (rid_ctr, h, tip) -> h

let (mk_mem : Prims.int -> FStar_Monotonic_HyperHeap.hmap -> unit -> mem') =
  fun rid_ctr -> fun h -> fun tip -> HS (rid_ctr, h, ())
let (get_hmap : mem' -> FStar_Monotonic_HyperHeap.hmap) =
  fun m -> __proj__HS__item__h m
let (get_rid_ctr : mem' -> Prims.int) = fun m -> __proj__HS__item__rid_ctr m

type mem = mem'
let (empty_mem : mem) =
  let empty_map =
    FStar_Map.restrict (FStar_Set.empty ())
      (FStar_Map.const FStar_Monotonic_Heap.emp) in
  let h = FStar_Map.upd empty_map () FStar_Monotonic_Heap.emp in
  mk_mem Prims.int_one h ()
type 'm poppable = unit
let remove_elt : 'a . 'a FStar_Set.set -> 'a -> 'a FStar_Set.set =
  fun s ->
    fun x ->
      FStar_Set.intersect s (FStar_Set.complement (FStar_Set.singleton x))
type ('m0, 'm1) popped = unit
let (pop : mem -> mem) =
  fun m0 ->
    let uu___ = ((get_hmap m0), (), (get_rid_ctr m0)) in
    match uu___ with
    | (h0, tip0, rid_ctr0) ->
        let dom = remove_elt (FStar_Map.domain h0) () in
        let h1 = FStar_Map.restrict dom h0 in mk_mem rid_ctr0 h1 ()
type ('a, 'rel) mreference' =
  | MkRef of unit * ('a, 'rel) FStar_Monotonic_Heap.mref 
let uu___is_MkRef : 'a 'rel . ('a, 'rel) mreference' -> Prims.bool =
  fun projectee -> true

let __proj__MkRef__item__ref :
  'a 'rel . ('a, 'rel) mreference' -> ('a, 'rel) FStar_Monotonic_Heap.mref =
  fun projectee -> match projectee with | MkRef (frame, ref) -> ref
type ('a, 'rel) mreference = ('a, 'rel) mreference'

let mk_mreference :
  'a 'rel .
    unit -> ('a, 'rel) FStar_Monotonic_Heap.mref -> ('a, 'rel) mreference
  = fun id -> fun r -> MkRef ((), r)
let as_ref :
  'uuuuu 'uuuuu1 .
    ('uuuuu, 'uuuuu1) mreference ->
      ('uuuuu, 'uuuuu1) FStar_Monotonic_Heap.mref
  = fun x -> __proj__MkRef__item__ref x
type ('a, 'rel) mstackref = ('a, 'rel) mreference
type ('a, 'rel) mref = ('a, 'rel) mreference
type ('a, 'rel) mmmstackref = ('a, 'rel) mreference
type ('a, 'rel) mmmref = ('a, 'rel) mreference
type ('i, 'a, 'rel) s_mref = ('a, 'rel) mreference
let (live_region : mem -> unit -> Prims.bool) =
  fun m -> fun i -> FStar_Map.contains (get_hmap m) ()
type ('a, 'rel, 'm, 's) contains = unit
type ('a, 'rel, 'r, 'm) unused_in = unit
type ('a, 'rel, 'm, 'r) contains_ref_in_its_region =
  ('a, 'rel, unit, unit) FStar_Monotonic_Heap.contains
type ('a, 'rel, 'r, 'm0, 'm1) fresh_ref = unit
type ('i, 'm0, 'm1) fresh_region = unit
let alloc :
  'a 'rel . unit -> 'a -> Prims.bool -> mem -> (('a, 'rel) mreference * mem)
  =
  fun id ->
    fun init ->
      fun mm ->
        fun m ->
          let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
          match uu___ with
          | (h, rid_ctr, tip) ->
              let uu___1 =
                FStar_Monotonic_Heap.alloc (FStar_Map.sel h ()) init mm in
              (match uu___1 with
               | (r, id_h) ->
                   let h1 = FStar_Map.upd h () id_h in
                   ((mk_mreference () r), (mk_mem rid_ctr h1 ())))
let free : 'a 'rel . ('a, 'rel) mreference -> mem -> mem =
  fun r ->
    fun m ->
      let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
      match uu___ with
      | (h, rid_ctr, tip) ->
          let i_h = FStar_Map.sel h () in
          let i_h1 = FStar_Monotonic_Heap.free_mm i_h (as_ref r) in
          let h1 = FStar_Map.upd h () i_h1 in mk_mem rid_ctr h1 ()
let upd_tot : 'a 'rel . mem -> ('a, 'rel) mreference -> 'a -> mem =
  fun m ->
    fun r ->
      fun v ->
        let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
        match uu___ with
        | (h, rid_ctr, tip) ->
            let i_h = FStar_Map.sel h () in
            let i_h1 = FStar_Monotonic_Heap.upd_tot i_h (as_ref r) v in
            let h1 = FStar_Map.upd h () i_h1 in mk_mem rid_ctr h1 ()
let sel_tot : 'a 'rel . mem -> ('a, 'rel) mreference -> 'a =
  fun m ->
    fun r ->
      FStar_Monotonic_Heap.sel_tot (FStar_Map.sel (get_hmap m) ()) (as_ref r)
type ('m0, 'm1) fresh_frame = unit
let (hs_push_frame : mem -> mem) =
  fun m ->
    let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
    match uu___ with
    | (h, rid_ctr, tip) ->
        let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp in
        mk_mem (rid_ctr + Prims.int_one) h1 ()
let (new_eternal_region :
  mem -> unit -> Prims.int FStar_Pervasives_Native.option -> (unit * mem)) =
  fun m ->
    fun parent ->
      fun c ->
        let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
        match uu___ with
        | (h, rid_ctr, tip) ->
            let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp in
            ((), (mk_mem (rid_ctr + Prims.int_one) h1 ()))
let (new_freeable_heap_region : mem -> unit -> (unit * mem)) =
  fun m ->
    fun parent ->
      let uu___ = ((get_hmap m), (get_rid_ctr m), ()) in
      match uu___ with
      | (h, rid_ctr, tip) ->
          let h1 = FStar_Map.upd h () FStar_Monotonic_Heap.emp in
          ((), (mk_mem (rid_ctr + Prims.int_one) h1 ()))
let (free_heap_region : mem -> unit -> mem) =
  fun m0 ->
    fun r ->
      let uu___ = ((get_hmap m0), (get_rid_ctr m0)) in
      match uu___ with
      | (h0, rid_ctr0) ->
          let dom = remove_elt (FStar_Map.domain h0) () in
          let h1 = FStar_Map.restrict dom h0 in mk_mem (get_rid_ctr m0) h1 ()
type ('s, 'm0, 'm1) modifies = unit
type ('s, 'm0, 'm1) modifies_transitively = unit
type 'm0 heap_only = unit
let (top_frame : mem -> FStar_Monotonic_Heap.heap) =
  fun m -> FStar_Map.sel (get_hmap m) ()
type ('id, 'h0, 'h1) modifies_one = unit
type ('id, 's, 'h0, 'h1) modifies_ref = unit
type some_ref =
  | Ref of unit * unit * (Obj.t, Obj.t) mreference 
let (uu___is_Ref : some_ref -> Prims.bool) = fun projectee -> true
let (__proj__Ref__item___2 : some_ref -> (unit, unit) mreference) =
  fun uu___ ->
    (fun projectee -> match projectee with | Ref (a, rel, _2) -> Obj.magic _2)
      uu___
type some_refs = some_ref Prims.list
let rec (regions_of_some_refs : some_refs -> unit FStar_Set.set) =
  fun rs ->
    match rs with
    | [] -> FStar_Set.empty ()
    | (Ref (uu___, uu___1, r))::tl ->
        FStar_Set.union (FStar_Set.singleton ()) (regions_of_some_refs tl)
type ('i, 'rs, 'h0, 'h1) modifies_some_refs = Obj.t
let (norm_steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.iota;
  FStar_Pervasives.zeta;
  FStar_Pervasives.delta;
  FStar_Pervasives.delta_only
    ["FStar.Monotonic.HyperStack.regions_of_some_refs";
    "FStar.Monotonic.HyperStack.refs_in_region";
    "FStar.Monotonic.HyperStack.modifies_some_refs"];
  FStar_Pervasives.primops]
type ('rs, 'h0, 'h1) mods = unit
type aref =
  | ARef of unit * FStar_Monotonic_Heap.aref 
let (uu___is_ARef : aref -> Prims.bool) = fun projectee -> true

let (__proj__ARef__item__aref_aref : aref -> FStar_Monotonic_Heap.aref) =
  fun projectee ->
    match projectee with | ARef (aref_region, aref_aref) -> aref_aref
let (dummy_aref : aref) = ARef ((), FStar_Monotonic_Heap.dummy_aref)
let aref_of : 'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) mreference -> aref =
  fun r -> ARef ((), (FStar_Monotonic_Heap.aref_of (as_ref r)))
type ('a, 'h) aref_unused_in = unit
type ('h, 'a, 'v, 'rel) aref_live_at = unit
let (reference_of : mem -> aref -> unit -> unit -> (Obj.t, Obj.t) mreference)
  =
  fun h ->
    fun a ->
      fun v ->
        fun rel ->
          MkRef
            ((),
              (FStar_Monotonic_Heap.ref_of
                 (FStar_Map.sel (__proj__HS__item__h h) ())
                 (__proj__ARef__item__aref_aref a) () ()))