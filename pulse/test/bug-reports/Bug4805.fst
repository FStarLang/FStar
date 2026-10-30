module Bug4805
#lang-pulse

(* Issue #4805: a typeclass method called on a dictionary binder, [d.step x],
   must be elaborated as a stateful call. *)

open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

class ops = {
  step: x:U32.t -> stt U32.t emp (fun _ -> emp);
}

fn run {| d:ops |} (x:U32.t)
requires emp
returns r:U32.t
ensures emp
{
  d.step x
}

fn run_let {| d:ops |} (x:U32.t)
requires emp
returns r:U32.t
ensures emp
{
  let y = d.step x;
  d.step y
}

noeq
type rcd = {
  f: x:U32.t -> stt U32.t emp (fun _ -> emp);
}

fn run_record (r:rcd) (x:U32.t)
requires emp
returns r:U32.t
ensures emp
{
  r.f x
}
