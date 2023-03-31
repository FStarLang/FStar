module Hacl.Meta

(* A snippet mimicking a piece of Hacl's specialize tactic. We keep it
here to test that it does not regress, including when using it as a
plugin. *)

open FStar.Tactics

let tm_unit = `()

[@@plugin]
let mk (nm:string) (msg:string) : Tac (list sigelt) =
  let quote_string (s:string) : term =
    pack_ln (Tv_Const (C_String s))
  in
  let se = pack_sigelt (Sg_Let false [
    pack_lb {
      lb_fv = pack_fv (cur_module () @ [nm]);
      lb_us = [];
      lb_typ = `int;
      lb_def = `(let x : unit = _ by (print (`#(quote_string msg)); exact tm_unit) in 42)
    }
  ]) in
  [se]
