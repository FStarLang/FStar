open Prims
type ('a, 'h, 'r) contains =
  ('a, unit, unit, unit) FStar_Monotonic_Heap.contains
type ('a, 'r, 'h) unused_in =
  ('a, unit, unit, unit) FStar_Monotonic_Heap.unused_in
type ('a, 'r, 'h0, 'h1) fresh = unit
let recall : 'uuuuu . 'uuuuu FStar_ST.ref -> unit =
  fun r -> FStar_ST.recall r
let alloc : 'uuuuu . 'uuuuu -> 'uuuuu FStar_ST.ref =
  fun init -> FStar_ST.alloc init
let read : 'uuuuu . 'uuuuu FStar_ST.ref -> 'uuuuu = fun r -> FStar_ST.read r
let write : 'uuuuu . 'uuuuu FStar_ST.ref -> 'uuuuu -> unit =
  fun r -> fun v -> FStar_ST.write r v
let op_Bang : 'uuuuu . 'uuuuu FStar_ST.ref -> 'uuuuu = fun r -> read r
let op_Colon_Equals : 'uuuuu . 'uuuuu FStar_ST.ref -> 'uuuuu -> unit =
  fun r -> fun v -> write r v