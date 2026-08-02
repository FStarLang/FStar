module MachineIntMatch

open Pulse
open Pulse.Lib.Pervasives

#lang-pulse

fn match_i8 (x:Int8.t)
  returns y:bool
{
  match x {
    0y -> { assert (pure (Int8.v x == 0)); true }
    _ -> { false }
  }
}

fn match_u8 (x:UInt8.t)
  returns y:bool
{
  match x {
    0uy -> { assert (pure (UInt8.v x == 0)); true }
    _ -> { false }
  }
}

fn match_i16 (x:Int16.t)
  returns y:bool
{
  match x {
    0s -> { assert (pure (Int16.v x == 0)); true }
    _ -> { false }
  }
}

fn match_u16 (x:UInt16.t)
  returns y:bool
{
  match x {
    0us -> { assert (pure (UInt16.v x == 0)); true }
    _ -> { false }
  }
}

fn match_i32 (x:Int32.t)
  returns y:Int32.t
{
  match x {
    -1l -> { assert (pure (Int32.v x == -1)); 9l }
    0l -> { assert (pure (Int32.v x == 0)); 10l }
    1l -> { assert (pure (Int32.v x == 1)); 11l }
    _ -> { x }
  }
}

fn match_i64 (x:Int64.t)
  returns y:bool
{
  match x {
    -1L -> { assert (pure (Int64.v x == -1)); true }
    _ -> { false }
  }
}

fn match_u64 (x:UInt64.t)
  returns y:bool
{
  match x {
    1uL -> { assert (pure (UInt64.v x == 1)); true }
    _ -> { false }
  }
}

fn match_sizet (x:SizeT.t)
  returns y:bool
{
  match x {
    1sz -> { assert (pure (SizeT.v x == 1)); true }
    _ -> { false }
  }
}

fn match_u32 (x:UInt32.t)
  returns y:UInt32.t
{
  match x {
    0ul -> { assert (pure (UInt32.v x == 0)); 10ul }
    1ul -> { assert (pure (UInt32.v x == 1)); 11ul }
    _ -> { x }
  }
}
