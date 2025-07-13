module InlineArrayLen

#lang-pulse
open Pulse

fn basic ()
  returns int
{
  let mut arr = [| 123; 2sz |];
  arr.(0sz);
}

inline_for_extraction noextract
fn gen (x : SizeT.t)
  requires pure (SizeT.v x > 0)
  returns int
{
  let mut arr = [| 123; x |];
  arr.(0sz);
}

fn use ()
  returns int
{
  gen 2sz;
}

inline_for_extraction noextract
fn gen_init (x : SizeT.t)
  (init : unit -> int)
  requires pure (SizeT.v x > 0)
  returns int
{
  let mut arr = [| init(); 2sz |];
  let r = arr.(0sz);
  r
}

fn use_gen_init ()
  returns int
{
  gen_init 2sz (fun _ -> 123);
}

inline_for_extraction noextract
fn gen_init_st (x : SizeT.t)
  (init : unit -> stt int emp (fun _ -> emp))
  requires pure (SizeT.v x > 0)
  returns int
{
  let mut arr = [| init(); 2sz |];
  let r = arr.(0sz);
  r
}

fn use_gen_init_st ()
  returns int
{
  fn init ()
    returns int
  {
    42;
  };
  gen_init_st 2sz init;
}

inline_for_extraction noextract
fn gen_len
  (len : (unit -> x:SizeT.t{SizeT.v x > 0}))
  returns int
{
  let mut arr = [| 123; len() |];
  let r = arr.(0sz);
  r
}

fn use_gen_len ()
  returns int
{
  gen_len (fun _ -> 2sz);
}

inline_for_extraction noextract
fn gen_len_st
  (len : unit -> stt SizeT.t emp (fun r -> pure (SizeT.v r > 0)))
  returns int
{
  let mut arr = [| 123; len () |];
  let r = arr.(0sz);
  r
}

fn use_gen_len_st ()
  returns int
{
  fn len ()
    returns r : SizeT.t
    ensures pure (SizeT.v r > 0)
  {
    42sz;
  };
  gen_len_st len;
}