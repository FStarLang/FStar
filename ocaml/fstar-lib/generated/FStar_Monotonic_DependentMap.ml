open Prims
type ('a, 'b, 'x) opt = 'b FStar_Pervasives_Native.option
type ('a, 'b) partial_dependent_map =
  ('a, ('a, 'b, unit) opt) FStar_DependentMap.t
let empty_partial_dependent_map :
  'a 'b . unit -> ('a, 'b) partial_dependent_map =
  fun uu___ ->
    FStar_DependentMap.create (fun x -> FStar_Pervasives_Native.None)
type ('a, 'b) map = ('a, 'b) Prims.dtuple2 Prims.list
let empty : 'a 'b . unit -> ('a, 'b) map = fun uu___ -> []
let rec sel : 'a 'b . ('a, 'b) map -> 'a -> 'b FStar_Pervasives_Native.option
  =
  fun r ->
    fun x ->
      match r with
      | [] -> FStar_Pervasives_Native.None
      | (Prims.Mkdtuple2 (x', y))::tl ->
          if x = x' then FStar_Pervasives_Native.Some y else sel tl x
let upd : 'a 'b . ('a, 'b) map -> 'a -> 'b -> ('a, 'b) map =
  fun r -> fun x -> fun v -> (Prims.Mkdtuple2 (x, v)) :: r
type ('a, 'b, 'inv) imap = ('a, 'b) map
type ('a, 'b, 'inv, 'm1, 'm2) grows' = unit
type ('a, 'b, 'inv, 'uuuuu, 'uuuuu1) grows = unit
type ('r, 'a, 'b, 'inv) t =
  (unit, ('a, 'b, 'inv) imap, unit) FStar_HyperStack_ST.m_rref
type ('a, 'b, 'inv, 'r, 't1, 'x, 'h) defined = unit
type ('a, 'b, 'inv, 'r, 't1, 'x, 'h) fresh = unit
type ('a, 'b, 'inv, 'r, 't1, 'x, 'y, 'h) contains = unit
let alloc : 'a 'b 'inv . unit -> unit -> (unit, 'a, 'b, 'inv) t =
  fun r -> fun uu___ -> FStar_HyperStack_ST.ralloc () []
let extend : 'a 'b 'inv . unit -> (unit, 'a, 'b, 'inv) t -> 'a -> 'b -> unit
  =
  fun r ->
    fun t1 ->
      fun x ->
        fun y ->
          FStar_HyperStack_ST.recall t1;
          (let cur = FStar_HyperStack_ST.op_Bang t1 in
           FStar_HyperStack_ST.op_Colon_Equals t1 (upd cur x y);
           FStar_HyperStack_ST.mr_witness () () () (Obj.magic t1) ())
let lookup :
  'a 'b 'inv .
    unit -> (unit, 'a, 'b, 'inv) t -> 'a -> 'b FStar_Pervasives_Native.option
  =
  fun r ->
    fun t1 ->
      fun x ->
        let m = FStar_HyperStack_ST.op_Bang t1 in
        let y = sel m x in
        match y with
        | FStar_Pervasives_Native.None -> y
        | FStar_Pervasives_Native.Some b1 ->
            (FStar_HyperStack_ST.mr_witness () () () (Obj.magic t1) (); y)
type ('a, 'b, 'inv, 'r, 't1, 'h, 'pred) forall_t = unit
let f_opt :
  'a 'b 'c .
    ('a -> 'b -> 'c) ->
      'a ->
        'b FStar_Pervasives_Native.option ->
          'c FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      fun y ->
        match y with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some y1 ->
            FStar_Pervasives_Native.Some (f x y1)
let rec mmap_f : 'a 'b 'c . ('a, 'b) map -> ('a -> 'b -> 'c) -> ('a, 'c) map
  =
  fun m ->
    fun f ->
      match m with
      | [] -> []
      | (Prims.Mkdtuple2 (x, y))::tl -> (Prims.Mkdtuple2 (x, (f x y))) ::
          (mmap_f tl f)
let map_f :
  'a 'b 'c 'inv 'invu .
    unit ->
      unit ->
        (unit, 'a, 'b, 'inv) t -> ('a -> 'b -> 'c) -> (unit, 'a, 'c, 'invu) t
  =
  fun r ->
    fun r' ->
      fun t1 ->
        fun f ->
          let m = FStar_HyperStack_ST.op_Bang t1 in
          FStar_HyperStack_ST.ralloc () (mmap_f m f)