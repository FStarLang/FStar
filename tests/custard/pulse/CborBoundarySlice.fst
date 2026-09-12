module CborBoundarySlice
#lang-pulse

(* A reduced deterministic-CBOR well-formedness checker over a byte slice.

   It is deliberately *not* the real EverParse parser.  It exists to keep
   exercising the four classes of behaviour that the curated CBOR corpus was
   built to hit, and that random input generation was measured not to reach:

     1. UTF-8 codepoint and continuation-byte boundaries,
     2. minimal-length integer encodings at each width boundary,
     3. declared element counts versus remaining input budget,
     4. truncation, i.e. proper prefixes of well-formed items.

   The input is a [Pulse.Lib.Slice.slice] over a stack-allocated array, which
   is what EverParse's own parsers take.  Direct-to-C compiles it to a
   [{ uint8_t *elt; size_t len; }] struct over a [uint8_t[N]], and the Rust
   column compiles it to a borrowed [&mut [u8]] over a [[u8; N]] with no
   [Box] -- the representation whose miscompilation section 19.15 is about.
   A test that merely built would not have caught that; this one writes the
   vector through the slice and then checks its own answers, so a write that
   lands in a temporary shows up as a wrong result.

   [main] reports through its exit code: direct-to-C has no krmllib, so there
   is no [FStar.IO.print_string] to link against.

   Regenerate with [CborBoundarySlice.gen.py]; reproduce the mutation-adequacy
   numbers in the accompanying README with [CborBoundarySlice.mutants.py]. *)

open Pulse
open Pulse.Lib.Slice

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Cast = FStar.Int.Cast

type byte = U8.t

let in_range (lo hi x : byte) : Tot bool = U8.lte lo x && U8.lte x hi

let arg_is_minimal (ai : byte) (v : U64.t) : Tot bool =
  if U8.eq ai 24uy then U64.gte v 24UL
  else if U8.eq ai 25uy then U64.gte v 256UL
  else if U8.eq ai 26uy then U64.gte v 65536UL
  else if U8.eq ai 27uy then U64.gte v 4294967296UL
  else true

let arg_width (ai : byte) : Tot (option U64.t) =
  if U8.lt ai 24uy then Some 0UL
  else if U8.eq ai 24uy then Some 1UL
  else if U8.eq ai 25uy then Some 2UL
  else if U8.eq ai 26uy then Some 4UL
  else if U8.eq ai 27uy then Some 8UL
  else None

fn peek (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte)) (i : U64.t)
  requires pts_to s #p v
  returns r : option byte
  ensures pts_to s #p v
{
  S.pts_to_len s;
  if (U64.lt i (SZ.sizet_to_uint64 (S.len s))) {
    let b = s.(SZ.uint64_to_sizet i); Some b
  } else { None #byte }
}

fn rem (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte)) (pos : U64.t)
  requires pts_to s #p v
  returns r : U64.t
  ensures pts_to s #p v
{
  S.pts_to_len s;
  let l = SZ.sizet_to_uint64 (S.len s);
  if (U64.lt pos l) { U64.sub l pos } else { 0UL }
}

fn rec take_be (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte))
                (n : U64.t) (acc : U64.t) (pos : U64.t)
  requires pts_to s #p v
  returns r : option U64.t
  ensures pts_to s #p v
  decreases (U64.v n)
{
  S.pts_to_len s;
  if (U64.eq n 0UL) { Some acc }
  else {
    match peek s pos {
      None -> { None #U64.t }
      Some b -> {
        take_be s (U64.sub n 1UL)
                  (U64.add_mod (U64.mul_mod acc 256UL) (Cast.uint8_to_uint64 b))
                  (U64.add_mod pos 1UL)
      }
    }
  }
}

fn rec utf8_take (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte))
                  (n : U64.t) (pos : U64.t)
  requires pts_to s #p v
  returns r : option U64.t
  ensures pts_to s #p v
  decreases (U64.v n)
{
  S.pts_to_len s;
  if (U64.eq n 0UL) { Some pos }
  else {
    match peek s pos {
      None -> { None #U64.t }
      Some b0 -> {
        if (U8.lte b0 0x7Fuy) {
          utf8_take s (U64.sub n 1UL) (U64.add_mod pos 1UL)
        } else if (in_range 0xC2uy 0xDFuy b0) {
          if (U64.lt n 2UL) { None #U64.t }
          else {
            match peek s (U64.add_mod pos 1UL) {
              None -> { None #U64.t }
              Some b1 -> {
                if (in_range 0x80uy 0xBFuy b1) {
                  utf8_take s (U64.sub n 2UL) (U64.add_mod pos 2UL)
                } else { None #U64.t }
              }
            }
          }
        } else if (U8.eq b0 0xE0uy || U8.eq b0 0xEDuy
                   || in_range 0xE1uy 0xECuy b0 || in_range 0xEEuy 0xEFuy b0) {
          if (U64.lt n 3UL) { None #U64.t }
          else {
            let lo1 = (if U8.eq b0 0xE0uy then 0xA0uy else 0x80uy);
            let hi1 = (if U8.eq b0 0xEDuy then 0x9Fuy else 0xBFuy);
            match peek s (U64.add_mod pos 1UL) {
              None -> { None #U64.t }
              Some b1 -> {
                if (not (in_range lo1 hi1 b1)) { None #U64.t }
                else {
                  match peek s (U64.add_mod pos 2UL) {
                    None -> { None #U64.t }
                    Some b2 -> {
                      if (in_range 0x80uy 0xBFuy b2) {
                        utf8_take s (U64.sub n 3UL) (U64.add_mod pos 3UL)
                      } else { None #U64.t }
                    }
                  }
                }
              }
            }
          }
        } else if (in_range 0xF0uy 0xF4uy b0) {
          if (U64.lt n 4UL) { None #U64.t }
          else {
            let lo1 = (if U8.eq b0 0xF0uy then 0x90uy else 0x80uy);
            let hi1 = (if U8.eq b0 0xF4uy then 0x8Fuy else 0xBFuy);
            match peek s (U64.add_mod pos 1UL) {
              None -> { None #U64.t }
              Some b1 -> {
                if (not (in_range lo1 hi1 b1)) { None #U64.t }
                else {
                  match peek s (U64.add_mod pos 2UL) {
                    None -> { None #U64.t }
                    Some b2 -> {
                      if (not (in_range 0x80uy 0xBFuy b2)) { None #U64.t }
                      else {
                        match peek s (U64.add_mod pos 3UL) {
                          None -> { None #U64.t }
                          Some b3 -> {
                            if (in_range 0x80uy 0xBFuy b3) {
                              utf8_take s (U64.sub n 4UL) (U64.add_mod pos 4UL)
                            } else { None #U64.t }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        } else { None #U64.t }
      }
    }
  }
}

fn rec items (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte))
              (fuel : U64.t) (n : U64.t) (pos : U64.t)
  requires pts_to s #p v
  returns r : option U64.t
  ensures pts_to s #p v
  decreases (U64.v fuel)
{
  S.pts_to_len s;
  if (U64.eq fuel 0UL) { None #U64.t }
  else if (U64.eq n 0UL) { Some pos }
  else {
    match peek s pos {
      None -> { None #U64.t }
      Some b0 -> {
        let mt = U8.shift_right b0 5ul;
        let ai = U8.logand b0 0x1Fuy;
        match arg_width ai {
          None -> { None #U64.t }
          Some w -> {
            match take_be s w 0UL (U64.add_mod pos 1UL) {
              None -> { None #U64.t }
              Some a -> {
                let av = (if U8.lt ai 24uy then Cast.uint8_to_uint64 ai else a);
                let after = U64.add_mod (U64.add_mod pos 1UL) w;
                if (not (arg_is_minimal ai av)) { None #U64.t }
                else {
                  let budget = rem s after;
                  let bud64 = budget;
                  if (U8.eq mt 0uy || U8.eq mt 1uy) {
                    items s (U64.sub fuel 1UL) (U64.sub n 1UL) after
                  } else if (U8.eq mt 2uy) {
                    if (U64.gt av bud64) { None #U64.t }
                    else {
                      items s (U64.sub fuel 1UL) (U64.sub n 1UL)
                            (U64.add_mod after av)
                    }
                  } else if (U8.eq mt 3uy) {
                    if (U64.gt av bud64) { None #U64.t }
                    else {
                      match utf8_take s av after {
                        None -> { None #U64.t }
                        Some q -> { items s (U64.sub fuel 1UL) (U64.sub n 1UL) q }
                      }
                    }
                  } else if (U8.eq mt 4uy) {
                    if (U64.gt av bud64) { None #U64.t }
                    else {
                      match items s (U64.sub fuel 1UL) av after {
                        None -> { None #U64.t }
                        Some q -> { items s (U64.sub fuel 1UL) (U64.sub n 1UL) q }
                      }
                    }
                  } else if (U8.eq mt 5uy) {
                    if (U64.gt av bud64) { None #U64.t }
                    else if (U64.gt av (U64.sub bud64 av)) { None #U64.t }
                    else {
                      match items s (U64.sub fuel 1UL)
                                   (U64.mul_mod av 2UL) after {
                        None -> { None #U64.t }
                        Some q -> { items s (U64.sub fuel 1UL) (U64.sub n 1UL) q }
                      }
                    }
                  } else if (U8.eq mt 6uy) {
                    match items s (U64.sub fuel 1UL) 1UL after {
                      None -> { None #U64.t }
                      Some q -> { items s (U64.sub fuel 1UL) (U64.sub n 1UL) q }
                    }
                  } else {
                    if (U8.lt ai 24uy) {
                      items s (U64.sub fuel 1UL) (U64.sub n 1UL) after
                    } else if (U8.eq ai 24uy) {
                      if (U64.gte av 32UL) {
                        items s (U64.sub fuel 1UL) (U64.sub n 1UL) after
                      } else { None #U64.t }
                    } else { None #U64.t }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

fn validate (s : S.slice byte) (#p : perm) (#v : erased (Seq.seq byte))
  requires pts_to s #p v
  returns r : bool
  ensures pts_to s #p v
{
  S.pts_to_len s;
  match items s 64UL 1UL 0UL {
    None -> { false }
    Some q -> { U64.eq q (SZ.sizet_to_uint64 (S.len s)) }
  }
}

(* Writing a test vector into a freshly allocated array one byte at a time
   makes the caller's context accumulate one [Seq.upd] per byte, and the
   length fact then has to be chased through the whole chain -- which the
   solver stops managing at around twenty bytes.  [put] hides the update
   behind an existential that keeps only the length, so the cost of a vector
   is linear in its size rather than quadratic. *)
fn put (s : S.slice byte) (#v : erased (Seq.seq byte)) (i : SZ.t) (b : byte)
  requires pts_to s v ** pure (SZ.v i < Seq.length v)
  ensures exists* v'. pts_to s v' ** pure (Seq.length v' == Seq.length v)
{
  s.(i) <- b;
}

fn v0 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 30sz |];
  A.pts_to_len a;
  let s = S.from_array a 30sz;
  S.pts_to_len s;
  put s 0sz 0xA3uy;
  put s 1sz 0x42uy;
  put s 2sz 0x6Fuy;
  put s 3sz 0xDDuy;
  put s 4sz 0xF8uy;
  put s 5sz 0x20uy;
  put s 6sz 0x45uy;
  put s 7sz 0x66uy;
  put s 8sz 0x72uy;
  put s 9sz 0xE7uy;
  put s 10sz 0x58uy;
  put s 11sz 0xB8uy;
  put s 12sz 0xD8uy;
  put s 13sz 0x64uy;
  put s 14sz 0x17uy;
  put s 15sz 0x60uy;
  put s 16sz 0x82uy;
  put s 17sz 0x39uy;
  put s 18sz 0xFFuy;
  put s 19sz 0xFFuy;
  put s 20sz 0xDBuy;
  put s 21sz 0xFFuy;
  put s 22sz 0xFFuy;
  put s 23sz 0xFFuy;
  put s 24sz 0xFFuy;
  put s 25sz 0xFFuy;
  put s 26sz 0xFFuy;
  put s 27sz 0xFFuy;
  put s 28sz 0xFFuy;
  put s 29sz 0xF7uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v1 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 58sz |];
  A.pts_to_len a;
  let s = S.from_array a 58sz;
  S.pts_to_len s;
  put s 0sz 0xDBuy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0x00uy;
  put s 4sz 0x01uy;
  put s 5sz 0x00uy;
  put s 6sz 0x00uy;
  put s 7sz 0x00uy;
  put s 8sz 0x00uy;
  put s 9sz 0xA2uy;
  put s 10sz 0x1Auy;
  put s 11sz 0x36uy;
  put s 12sz 0x42uy;
  put s 13sz 0xC8uy;
  put s 14sz 0x4Buy;
  put s 15sz 0xA3uy;
  put s 16sz 0x1Auy;
  put s 17sz 0x9Cuy;
  put s 18sz 0xF4uy;
  put s 19sz 0xDAuy;
  put s 20sz 0x8Buy;
  put s 21sz 0xF8uy;
  put s 22sz 0xFFuy;
  put s 23sz 0x45uy;
  put s 24sz 0xA2uy;
  put s 25sz 0xE6uy;
  put s 26sz 0x78uy;
  put s 27sz 0x37uy;
  put s 28sz 0xDFuy;
  put s 29sz 0x6Buy;
  put s 30sz 0xE4uy;
  put s 31sz 0xB8uy;
  put s 32sz 0xADuy;
  put s 33sz 0xC3uy;
  put s 34sz 0xA9uy;
  put s 35sz 0x5Auy;
  put s 36sz 0x62uy;
  put s 37sz 0xF0uy;
  put s 38sz 0x9Fuy;
  put s 39sz 0x98uy;
  put s 40sz 0x80uy;
  put s 41sz 0x65uy;
  put s 42sz 0x63uy;
  put s 43sz 0x64uy;
  put s 44sz 0x63uy;
  put s 45sz 0x65uy;
  put s 46sz 0x65uy;
  put s 47sz 0x44uy;
  put s 48sz 0x7Fuy;
  put s 49sz 0x6Duy;
  put s 50sz 0xF2uy;
  put s 51sz 0x24uy;
  put s 52sz 0x1Auy;
  put s 53sz 0xB6uy;
  put s 54sz 0x6Cuy;
  put s 55sz 0x10uy;
  put s 56sz 0x8Euy;
  put s 57sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v2 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 2sz |];
  A.pts_to_len a;
  let s = S.from_array a 2sz;
  S.pts_to_len s;
  put s 0sz 0x61uy;
  put s 1sz 0x7Fuy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v3 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x62uy;
  put s 1sz 0xDFuy;
  put s 2sz 0xBFuy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v4 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xE0uy;
  put s 2sz 0xA0uy;
  put s 3sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v5 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xEDuy;
  put s 2sz 0x9Fuy;
  put s 3sz 0xBFuy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v6 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xEEuy;
  put s 2sz 0x80uy;
  put s 3sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v7 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xEFuy;
  put s 2sz 0xBFuy;
  put s 3sz 0xBFuy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v8 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF0uy;
  put s 2sz 0x90uy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v9 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF4uy;
  put s 2sz 0x8Fuy;
  put s 3sz 0xBFuy;
  put s 4sz 0xBFuy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v10 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xE1uy;
  put s 2sz 0x80uy;
  put s 3sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v11 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 7sz |];
  A.pts_to_len a;
  let s = S.from_array a 7sz;
  S.pts_to_len s;
  put s 0sz 0xA2uy;
  put s 1sz 0x18uy;
  put s 2sz 0x18uy;
  put s 3sz 0x00uy;
  put s 4sz 0x61uy;
  put s 5sz 0x61uy;
  put s 6sz 0x01uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v12 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x1Auy;
  put s 1sz 0x00uy;
  put s 2sz 0x01uy;
  put s 3sz 0x00uy;
  put s 4sz 0x00uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v13 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x39uy;
  put s 1sz 0x01uy;
  put s 2sz 0x00uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v14 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF1uy;
  put s 2sz 0x80uy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v15 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x62uy;
  put s 1sz 0xC2uy;
  put s 2sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v16 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 1sz |];
  A.pts_to_len a;
  let s = S.from_array a 1sz;
  S.pts_to_len s;
  put s 0sz 0xA0uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v17 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 1sz |];
  A.pts_to_len a;
  let s = S.from_array a 1sz;
  S.pts_to_len s;
  put s 0sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v18 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 2sz |];
  A.pts_to_len a;
  let s = S.from_array a 2sz;
  S.pts_to_len s;
  put s 0sz 0x81uy;
  put s 1sz 0x00uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v19 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x82uy;
  put s 1sz 0x00uy;
  put s 2sz 0x01uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v20 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x83uy;
  put s 1sz 0x00uy;
  put s 2sz 0x01uy;
  put s 3sz 0x02uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v21 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0xA1uy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v22 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0xA2uy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0x01uy;
  put s 4sz 0x01uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v23 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 7sz |];
  A.pts_to_len a;
  let s = S.from_array a 7sz;
  S.pts_to_len s;
  put s 0sz 0xA3uy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0x01uy;
  put s 4sz 0x01uy;
  put s 5sz 0x02uy;
  put s 6sz 0x02uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v24 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xE1uy;
  put s 2sz 0xBFuy;
  put s 3sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v25 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF1uy;
  put s 2sz 0xBFuy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = true)
}

fn v26 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF4uy;
  put s 2sz 0x90uy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v27 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xEDuy;
  put s 2sz 0xA0uy;
  put s 3sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v28 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x62uy;
  put s 1sz 0xC1uy;
  put s 2sz 0xBFuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v29 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x62uy;
  put s 1sz 0xC2uy;
  put s 2sz 0x7Fuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v30 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xE0uy;
  put s 2sz 0x9Fuy;
  put s 3sz 0xBFuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v31 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF0uy;
  put s 2sz 0x8Fuy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v32 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF5uy;
  put s 2sz 0x80uy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v33 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 2sz |];
  A.pts_to_len a;
  let s = S.from_array a 2sz;
  S.pts_to_len s;
  put s 0sz 0x61uy;
  put s 1sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v34 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF0uy;
  put s 2sz 0x90uy;
  put s 3sz 0xC0uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v35 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF0uy;
  put s 2sz 0x90uy;
  put s 3sz 0x80uy;
  put s 4sz 0xC0uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v36 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 2sz |];
  A.pts_to_len a;
  let s = S.from_array a 2sz;
  S.pts_to_len s;
  put s 0sz 0xF8uy;
  put s 1sz 0x1Fuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v37 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 2sz |];
  A.pts_to_len a;
  let s = S.from_array a 2sz;
  S.pts_to_len s;
  put s 0sz 0x18uy;
  put s 1sz 0x17uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v38 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x19uy;
  put s 1sz 0x00uy;
  put s 2sz 0xFFuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v39 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x1Auy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0xFFuy;
  put s 4sz 0xFFuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v40 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 9sz |];
  A.pts_to_len a;
  let s = S.from_array a 9sz;
  S.pts_to_len s;
  put s 0sz 0x3Buy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0x00uy;
  put s 4sz 0x00uy;
  put s 5sz 0xFFuy;
  put s 6sz 0xFFuy;
  put s 7sz 0xFFuy;
  put s 8sz 0xFFuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v41 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 7sz |];
  A.pts_to_len a;
  let s = S.from_array a 7sz;
  S.pts_to_len s;
  put s 0sz 0x85uy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0x00uy;
  put s 4sz 0x00uy;
  put s 5sz 0x00uy;
  put s 6sz 0x00uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v42 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 1sz |];
  A.pts_to_len a;
  let s = S.from_array a 1sz;
  S.pts_to_len s;
  put s 0sz 0x18uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v43 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 2sz |];
  A.pts_to_len a;
  let s = S.from_array a 2sz;
  S.pts_to_len s;
  put s 0sz 0x19uy;
  put s 1sz 0xFFuy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v44 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 3sz |];
  A.pts_to_len a;
  let s = S.from_array a 3sz;
  S.pts_to_len s;
  put s 0sz 0x1Auy;
  put s 1sz 0x01uy;
  put s 2sz 0x00uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v45 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 6sz |];
  A.pts_to_len a;
  let s = S.from_array a 6sz;
  S.pts_to_len s;
  put s 0sz 0x1Buy;
  put s 1sz 0x00uy;
  put s 2sz 0x00uy;
  put s 3sz 0x00uy;
  put s 4sz 0x00uy;
  put s 5sz 0x01uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v46 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 4sz |];
  A.pts_to_len a;
  let s = S.from_array a 4sz;
  S.pts_to_len s;
  put s 0sz 0x63uy;
  put s 1sz 0xE1uy;
  put s 2sz 0xC0uy;
  put s 3sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn v47 ()
  requires emp
  returns r : bool
  ensures emp
{
  let mut a = [| 0uy; 5sz |];
  A.pts_to_len a;
  let s = S.from_array a 5sz;
  S.pts_to_len s;
  put s 0sz 0x64uy;
  put s 1sz 0xF1uy;
  put s 2sz 0xC0uy;
  put s 3sz 0x80uy;
  put s 4sz 0x80uy;
  let r = validate s;
  S.to_array s;
  (r = false)
}

fn g0 ()
  requires emp
  returns r : bool
  ensures emp
{
  let x0 = v0 ();
  let x1 = v1 ();
  let x2 = v2 ();
  let x3 = v3 ();
  let x4 = v4 ();
  let x5 = v5 ();
  let x6 = v6 ();
  let x7 = v7 ();
  let x8 = v8 ();
  let x9 = v9 ();
  let x10 = v10 ();
  let x11 = v11 ();
  let x12 = v12 ();
  let x13 = v13 ();
  let x14 = v14 ();
  let x15 = v15 ();
  x0 && x1 && x2 && x3 && x4 && x5 && x6 && x7 && x8 && x9 && x10 && x11 && x12 && x13 && x14 && x15
}

fn g1 ()
  requires emp
  returns r : bool
  ensures emp
{
  let x16 = v16 ();
  let x17 = v17 ();
  let x18 = v18 ();
  let x19 = v19 ();
  let x20 = v20 ();
  let x21 = v21 ();
  let x22 = v22 ();
  let x23 = v23 ();
  let x24 = v24 ();
  let x25 = v25 ();
  let x26 = v26 ();
  let x27 = v27 ();
  let x28 = v28 ();
  let x29 = v29 ();
  let x30 = v30 ();
  let x31 = v31 ();
  x16 && x17 && x18 && x19 && x20 && x21 && x22 && x23 && x24 && x25 && x26 && x27 && x28 && x29 && x30 && x31
}

fn g2 ()
  requires emp
  returns r : bool
  ensures emp
{
  let x32 = v32 ();
  let x33 = v33 ();
  let x34 = v34 ();
  let x35 = v35 ();
  let x36 = v36 ();
  let x37 = v37 ();
  let x38 = v38 ();
  let x39 = v39 ();
  let x40 = v40 ();
  let x41 = v41 ();
  let x42 = v42 ();
  let x43 = v43 ();
  let x44 = v44 ();
  let x45 = v45 ();
  let x46 = v46 ();
  let x47 = v47 ();
  x32 && x33 && x34 && x35 && x36 && x37 && x38 && x39 && x40 && x41 && x42 && x43 && x44 && x45 && x46 && x47
}

fn main ()
  requires emp
  returns r : FStar.Int32.t
  ensures emp
{
  let y0 = g0 ();
  let y1 = g1 ();
  let y2 = g2 ();
  if (y0 && y1 && y2) { 0l } else { 1l }
}
