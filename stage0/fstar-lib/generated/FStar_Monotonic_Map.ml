open Prims
type ('a, 'b) map' = 'a -> 'b FStar_Pervasives_Native.option
type ('a, 'b, 'inv) map = ('a, 'b) map'
let upd : 'a 'b . ('a, 'b) map' -> 'a -> 'b -> ('a, 'b) map' =
  fun m ->
    fun x ->
      fun y -> fun z -> if x = z then FStar_Pervasives_Native.Some y else m z
let sel : 'a 'b . ('a, 'b) map' -> 'a -> 'b FStar_Pervasives_Native.option =
  fun m -> fun x -> m x
type ('a, 'b, 'inv, 'm1, 'm2) grows_aux = unit
type ('a, 'b, 'inv, 'uuuuu, 'uuuuu1) grows = unit
type ('r, 'a, 'b, 'inv) t =
  (unit, ('a, 'b, 'inv) map, unit) FStar_HyperStack_ST.m_rref
let empty_map : 'a 'b . ('a, 'b) map' = fun x -> FStar_Pervasives_Native.None
type rid = unit
let (alloc : unit -> unit -> unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) t) =
  fun r ->
    fun a -> fun b -> fun inv -> FStar_HyperStack_ST.ralloc () empty_map
type ('r, 'a, 'b, 'inv, 'm, 'x, 'h) defined = unit
type ('r, 'a, 'b, 'inv, 'm, 'x, 'y, 'h) contains = unit
type ('r, 'a, 'b, 'inv, 'm, 'x, 'h) fresh = unit
let (extend :
  unit ->
    unit ->
      unit -> unit -> (unit, Obj.t, Obj.t, Obj.t) t -> Obj.t -> Obj.t -> unit)
  =
  fun r ->
    fun a ->
      fun b ->
        fun inv ->
          fun m ->
            fun x ->
              fun y ->
                FStar_HyperStack_ST.recall m;
                (let cur = FStar_HyperStack_ST.op_Bang m in
                 FStar_HyperStack_ST.op_Colon_Equals m (upd cur x y);
                 FStar_HyperStack_ST.mr_witness () () () (Obj.magic m) ();
                 FStar_HyperStack_ST.mr_witness () () () (Obj.magic m) ())
let (lookup :
  unit ->
    unit ->
      unit ->
        unit ->
          (unit, Obj.t, Obj.t, Obj.t) t ->
            Obj.t -> Obj.t FStar_Pervasives_Native.option)
  =
  fun r ->
    fun a ->
      fun b ->
        fun inv ->
          fun m ->
            fun x ->
              let y =
                let uu___ = FStar_HyperStack_ST.op_Bang m in sel uu___ x in
              match y with
              | FStar_Pervasives_Native.None -> y
              | FStar_Pervasives_Native.Some b1 ->
                  (FStar_HyperStack_ST.mr_witness () () () (Obj.magic m) ();
                   FStar_HyperStack_ST.mr_witness () () () (Obj.magic m) ();
                   y)