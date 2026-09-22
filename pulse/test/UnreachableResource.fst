module UnreachableResource
open Pulse
module R = Pulse.Lib.Reference
#lang-pulse

// Native Pulse cases for FStarLang/pal#322.

// Reproductions: these fail on unmodified df3e072959.

fn early_return_read (p: R.ref int)
  returns r: int
{
  if true { return 7; } else {};
  return !p;
}

fn early_return_unreachable_read (p: R.ref int)
  returns r: int
{
  if true { return 7; } else {};
  unreachable ();
  return !p;
}

fn early_return_explicit_read (p: R.ref int)
  returns r: int
{
  if true { return 7; } else {};
  return R.read p #(FStar.Ghost.hide 0) #1.0R;
}

fn early_return_assert_explicit_read (p: R.ref int)
  returns r: int
{
  if true { return 7; } else {};
  assert (pure False);
  return R.read p #(FStar.Ghost.hide 0) #1.0R;
}

fn false_pre_read (p: R.ref int)
  requires pure False
  returns r: int
{
  return !p;
}

fn false_pre_explicit_read (p: R.ref int)
  requires pure False
  returns r: int
{
  return R.read p #(FStar.Ghost.hide 0) #1.0R;
}

fn false_pre_unreachable_read (p: R.ref int)
  requires pure False
  returns r: int
{
  unreachable ();
  return !p;
}

// Before the fix, this case failed when reconstructing the conditional postcondition,
// with R.pts_to p v already present, rather than at the read.
fn conditional_ownership (b: bool) (p: R.ref int) (v: int)
  requires (if b then emp else R.pts_to p v)
  returns r: int
  ensures (if b then emp else R.pts_to p v)
{
  if b { return 7; } else {};
  return !p;
}

// Positive controls.

fn early_return_assert_false (p: R.ref int)
  returns r: int
{
  if true { return 7; } else {};
  assert (pure False);
  return 0;
}

fn early_return_unreachable_explicit_read (p: R.ref int)
  returns r: int
{
  if true { return 7; } else {};
  unreachable ();
  return R.read p #(FStar.Ghost.hide 0) #1.0R;
}

fn early_return_explicit_read_post (p: R.ref int)
  returns r: int
  ensures pure (r == 7)
{
  if true { return 7; } else {};
  unreachable ();
  return R.read p #(FStar.Ghost.hide 0) #1.0R;
}

fn false_pre_unreachable_explicit_read (p: R.ref int)
  requires pure False
  returns r: int
{
  unreachable ();
  return R.read p #(FStar.Ghost.hide 0) #1.0R;
}

fn owned_read (p: R.ref int) (v: int)
  preserves R.pts_to p v
  returns r: int
  ensures pure (r == v)
{
  return !p;
}

fn symbolic_early_return (b: bool) (p: R.ref int)
  requires pure (b == true)
  returns r: int
  ensures pure (r == 7)
{
  if b { return 7; } else {};
  return !p;
}

fn polymorphic_false_pre (#a: Type0) (p: R.ref a)
  requires pure False
  returns r: a
{
  return !p;
}

fn polymorphic_unreachable_pre (#a: Type0) (p: R.ref a)
  requires is_unreachable
  returns r: a
{
  return !p;
}

fn unreachable_write (p: R.ref int)
  requires pure False
{
  p := 42;
}

fn conditional_ownership_reverse (b: bool) (p: R.ref int) (v: int)
  requires (if b then R.pts_to p v else emp)
  returns r: int
  ensures (if b then R.pts_to p v else emp)
{
  if b {} else { return 7; };
  return !p;
}
