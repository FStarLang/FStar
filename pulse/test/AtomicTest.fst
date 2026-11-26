module AtomicTest
#lang-pulse
open Pulse
open Pulse.Lib.Atomic
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SZ = FStar.SizeT

(* fetch_add and strong CAS on a 64-bit counter (issue #4671). *)
fn counter_u64 ()
  returns x: U64.t
  ensures pure (x == 10UL)
{
  let b = alloc_box 1UL;
  let old = fetch_add_box b 2UL;
  assert pure (old == 1UL);
  let ok = compare_exchange_box b 3UL 10UL;
  if ok {
    let x = load_box b;
    free_box b;
    x
  } else {
    unreachable ()
  }
}

fn flag_bool (b: atomic_box bool)
  requires b |-> false
  returns old: bool
  ensures b |-> true
{
  exchange_box b true
}

fn bits_u8 (r: atomic_ref U8.t) (#v: erased U8.t)
  requires r |-> v
  ensures r |-> U8.logxor (U8.logor (U8.logand v 0xF0uy) 0x01uy) 0x03uy
{
  let _ = fetch_and r 0xF0uy;
  let _ = fetch_or r 0x01uy;
  let _ = fetch_xor r 0x03uy;
  ()
}

fn sub_u32 (r: atomic_ref U32.t) (#v: erased U32.t)
  requires r |-> v
  returns old: U32.t
  ensures r |-> U32.sub_mod v 1ul
{
  fetch_sub r 1ul
}

fn store_sizet (r: atomic_ref SZ.t) (x: SZ.t) (#v: erased SZ.t)
  requires r |-> v
  ensures r |-> x
{
  store r x
}

fn cas_i64 (r: atomic_ref Int64.t) (#v: erased Int64.t)
  requires r |-> v
  returns ok: bool
  ensures (if ok then (r |-> 1L) ** pure (reveal v == 0L) else (r |-> v) ** pure (reveal v =!= 0L))
{
  compare_exchange r 0L 1L
}

fn read_shared (r: atomic_ref U64.t) (#p: perm) (#v: erased U64.t)
  preserves r |-> Frac p v
  returns x: U64.t
  ensures rewrites_to x (reveal v)
{
  share r;
  let x = load r;
  gather r;
  x
}
