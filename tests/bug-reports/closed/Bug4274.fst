module Bug4274

#lang-pulse
open Pulse

noeq type foo = {
  x: ref int;
  y: ref int;
  z: ref (ref int);
}

[@@erasable] noeq type foo_spec = {
  x': int;
  y': int;
  z': ref int; z'': int;
}

let foo_pred ([@@@mkey]x: foo) (y: foo_spec) : slprop =
  pts_to x.x y.x' ** pts_to x.y y.y'
  ** pts_to x.z y.z' ** pts_to y.z' y.z''

[@@pulse_intro]
ghost fn foo_pred_unfold x y
  requires foo_pred x y
  ensures Pulse.Lib.Reference.pts_to x.x y.x'
  ensures Pulse.Lib.Reference.pts_to x.y y.y'
  ensures Pulse.Lib.Reference.pts_to x.z y.z'
  ensures Pulse.Lib.Reference.pts_to y.z' y.z''
{
  unfold foo_pred;
}

[@@pulse_intro]
ghost fn foo_pred_fold x vx vy vz vz'
  requires Pulse.Lib.Reference.pts_to x.x vx
  requires Pulse.Lib.Reference.pts_to x.y vy
  requires Pulse.Lib.Reference.pts_to x.z vz
  requires Pulse.Lib.Reference.pts_to vz vz'
  ensures foo_pred x ({x'=vx;y'=vy;z'=vz;z''=vz'})
{
  fold foo_pred x ({x'=vx;y'=vy;z'=vz;z''=vz'});
}

fn read_x (x: foo)
  preserves foo_pred x 'vx
  returns _: int
{
  let tmp = !x.x;
  x.x := 42 + tmp;
  x.x := (!x.x) - 42;
  tmp
}

let foo_value (x: foo) #y = observe (foo_pred x) #y

#set-options "--ext pulse:admit_diag=1"

fn write_x (x: foo)
  preserves exists* vx. foo_pred x vx
  ensures pure ((foo_value x).x' == 10)
{
  x.x := 10;
  assert foo_pred x _;
  x.y := !x.x;
  assert foo_pred x _;
  admit();
(*
- Current context:
    foo_pred x
      (Mkfoo_spec (Mkfoo_spec 10 vx.y' vx.z' vx.z'').x'
          (Mkfoo_spec 10 vx.y' vx.z' vx.z'').x'
          (Mkfoo_spec 10 vx.y' vx.z' vx.z'').z'
          (Mkfoo_spec 10 vx.y' vx.z' vx.z'').z'')
*)
}
