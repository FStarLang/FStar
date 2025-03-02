module BinderAttrs

#lang-pulse
open Pulse.Nolib
open FStar.Tactics.V2

assume
val f1 ([@@@123] x:int) :
  stt int emp (fun _ -> emp)

fn f2 ([@@@123] x:int)
  requires emp
  returns  int
  ensures  emp
{ 1 }

(* f1 and f2 should both have the same binder attributes. *)

let typ_of (nm : string) : Tac typ =
  let tm = pack (Tv_FVar (pack_fv (explode_qn nm))) in
  tc (cur_env ()) tm

let check (t : typ) : Tac unit =
  match t with
  | Tv_Arrow b _c -> (
    match b.attrs with
    | [] -> fail "no attrs"
    | _ -> ()
  )
  | _ ->
    fail "not an arrow"

let _ = assert True by check (typ_of (`%f1))

[@@expect_failure] (* should work, Pulse currently dropping binder attrs *)
let _ = assert True by check (typ_of (`%f2))
