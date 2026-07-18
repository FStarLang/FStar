module LocalFnAnnot
open Pulse.Nolib
#lang-pulse

let t (p: slprop) = unit -> stt unit (requires p) (ensures fun _ -> emp)

fn f (p: slprop) requires p {
  fn g (q: slprop) (x: nat) : t (p ** q) = a {
    drop_ p;
    drop_ q;
  };
  g emp 42 ()
}