module MonoAttrI
#lang-pulse
open Pulse
module SZ = FStar.SizeT

fn f ([@@@FStar.Attributes.monomorphize] n: SZ.t)
  returns x: SZ.t
  ensures emp
{
  SZ.div n 2sz
}

fn main ()
  returns x: FStar.Int32.t
{
  let a = f 16sz;
  let b = f 32sz;
  if (SZ.eq a 8sz) { if (SZ.eq b 16sz) { 0l } else { 1l } } else { 1l }
}
