module Extend

open FStar.Tactics.V2
open FStar.Tactics.Typeclasses
module U32 = FStar.UInt32

(* A class representing that a nat x can be made
concrete as a U32. *)
class concrete (x:nat) = {
  c  : U32.t;
  pf : squash (eq2 #int (U32.v c) x);
}

(* We can define instances for some constants... but not all *)
instance concrete_0 : concrete 0 = { c = 0ul; pf = (); }
instance concrete_1 : concrete 1 = { c = 1ul; pf = (); }

exception Skip

let mk_u32 (n:int) : term = `(U32.uint_to_t (`#(Tv_Const (C_Int n))))

(* But we can construct these instances on the fly via a tactic *)
let mk_concrete () : Tac unit =
  match hua (cur_goal ()) with
  | Some (fv, _, args) ->
    if implode_qn (inspect_fv fv) = `%concrete then (
      match args with
      | [(t, Q_Explicit)] -> (
        match t with
        | Tv_Const (C_Int n) ->
          (* Ideally this just be
               exact (`Mkconcrete (`#mi) ())
             but that fails since we disable subtyping in the
             presence of uvars for t_exact... why? *)
          let mi = mk_u32 n in
          let pf = tcut (`squash (U32.v (`#mi) == `#t)) in
          let tm = `Mkconcrete (`#mi) (`#pf) in
          exact tm
        | _ ->
          raise Skip
      )
      | _ ->
        raise Skip
    )
    else
      raise Skip
  | _ ->
    raise Skip

let _ : concrete 2 = _ by (mk_concrete ())
let _ : concrete 3 = _ by (mk_concrete ())
let _ : concrete 4 = _ by (mk_concrete ())

(* It only works for constants, of course. *)
[@@expect_failure]
let nope (x:nat) : concrete x = _ by (mk_concrete ())

(* TODO: Extend typeclass resolution to allow
         to register `mk_concrete` as an extension? *)
