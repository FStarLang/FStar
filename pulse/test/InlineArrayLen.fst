module InlineArrayLen

#lang-pulse
open Pulse

fn basic ()
  returns Int32.t
{
  let mut arr = [| 123l; 2sz |];
  arr.(0sz);
}

inline_for_extraction noextract
fn gen (x : SizeT.t)
  requires pure (SizeT.v x > 0)
  returns Int32.t
{
  let mut arr = [| 123l; x |];
  arr.(0sz);
}

fn use ()
  returns Int32.t
{
  gen 2sz;
}

inline_for_extraction noextract
fn gen_init (x : SizeT.t)
  (init : unit -> Int32.t)
  requires pure (SizeT.v x > 0)
  returns Int32.t
{
  let mut arr = [| init(); 2sz |];
  let r = arr.(0sz);
  r
}

fn use_gen_init ()
  returns Int32.t
{
  gen_init 2sz (fun _ -> 123l);
}

inline_for_extraction noextract
fn gen_init_st (x : SizeT.t)
  (init : unit -> stt Int32.t emp (fun _ -> emp))
  requires pure (SizeT.v x > 0)
  returns Int32.t
{
  let mut arr = [| init(); 2sz |];
  let r = arr.(0sz);
  r
}

fn use_gen_init_st ()
  returns Int32.t
{
  gen_init_st 2sz fn _{ 123l };
}

inline_for_extraction noextract
fn gen_len
  (len : (unit -> x:SizeT.t{SizeT.v x > 0}))
  returns Int32.t
{
  let mut arr = [| 123l; len() |];
  let r = arr.(0sz);
  r
}

fn use_gen_len ()
  returns Int32.t
{
  gen_len (fun _ -> 2sz);
}

inline_for_extraction noextract
fn gen_len_st
  (len : unit -> stt SizeT.t emp (fun r -> pure (SizeT.v r > 0)))
  returns Int32.t
{
  let mut arr = [| 123l; len () |];
  let r = arr.(0sz);
  r
}

fn use_gen_len_st ()
  returns Int32.t
{
  gen_len_st fn _{ 42sz };
}