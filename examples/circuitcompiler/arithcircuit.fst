module Arith_Circuit
open Fixnat
open Wires

type circuitelt =
| Gate of natop * wrange * wrange * wrange
| Const of r:wrange{rsize r = natsize} * (fixnat natsize)

type circuit = list circuitelt

type env = nat

val genvalue: g:env -> v:value -> Tot (env*(circuit*wrange))
let genvalue g value =
  match value with
  | V_nat n ->
    let g',r = alloc_wrange g natsize in
    g',([Const(r,n)],r)

val genexpr: g:env -> e:expr -> Tot (env*(circuit*wrange)) (decreases %[e;g])
let rec genexpr g expr =
  match expr with
  | E_value v -> genvalue g v
  | E_natop (op,e1,e2) ->
    let g1,(c1,r1) = genexpr g e1 in
    let g2,(c2,r2) = genexpr g1 e2 in
    let g3,r = alloc_wrange g2 natsize in
    g3, (c1 @ c2 @ [Gate(op, r, r1, r2)], r)

(* TODO: Make a semantics for circuits and make a semantics for expressions, proving the two equivalent. *)
