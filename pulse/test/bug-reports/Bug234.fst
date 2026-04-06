module Bug234
#lang-pulse
open Pulse

type a =
type b =
type c =
type d =
type f =

let ok (x:a) (y:b) (z:c) (w:d) (u:f) : slprop =
  emp

let ty (x:a) (y:b) (z:c) (w:d) = u:f -> stt unit emp (fun r -> ok x y z w u)

fn foo x y z w : ty x y z w  = u {
  fold ok x y z w u;
}
