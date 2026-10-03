(*
   The universe of a total effect's computation type is the universe of its
   REPRESENTATION, not of its result type.

   `FStarC.TypeChecker.Util.universe_of_comp` used to answer

       if M is pure/ghost or marked `total` then u_res else u#0

   which is unsound for any total effect whose `repr` does not preserve
   universes.  With

       let repr (a:Type u#a) : Type u#(max a 1) = (t:Type u#0 & a)

   the value that inhabits `M bool` is a `(t:Type u#0 & bool)`, which lives in
   `Type u#1`; reporting `u#0` puts a `Type u#1` value inside a type classified
   `Type u#0`, i.e. it embeds `Type u#0` into `Type u#0`.

   `Env.effect_universe` now answers with the universe that `TcEffect` read off
   the effect's own `repr` when the effect was declared, and
   `FStarC.TypeChecker.Core.check_comp` -- which already computed the universe
   of the representation, and so already disagreed with the main typechecker --
   consults the same function.

   Note that the rule cuts both ways: a `repr` that LOWERS the universe (M2
   below) makes the computation type smaller than its result type, which the
   old rule got wrong in the sound direction.
*)
module SimpleEffects_ReprUniverse

(** 1. A universe-preserving representation: [M0 t] sits where [t] does. *)

let id_repr (a:Type u#a) : Type u#a = a
let id_return (a:Type u#a) (x:a) : id_repr a = x
let id_bind (a:Type u#a) (b:Type u#b) (f:id_repr a) (g:a -> id_repr b) : id_repr b = g f

total reifiable reflectable effect {
  M0 with { repr = id_repr; return = id_return; bind = id_bind }
}

let m0_small : Type u#0 = unit -> M0 bool       (requires True) (ensures fun _ -> True)
let m0_big   : Type u#1 = unit -> M0 (Type u#0) (requires True) (ensures fun _ -> True)

[@@expect_failure [189]]
let m0_too_small : Type u#0 = unit -> M0 (Type u#0) (requires True) (ensures fun _ -> True)

(** 2. A universe-RAISING representation: [M1 t] sits one level above [t].
       This is the case the old rule got wrong. *)

let m_repr (a:Type u#a) : Type u#(max a 1) = (t:Type u#0 & a)
let m_return (a:Type u#a) (x:a) : m_repr a = (| unit, x |)
let m_bind (a:Type u#a) (b:Type u#b) (f:m_repr a) (g:a -> m_repr b) : m_repr b =
  (| dfst f, dsnd (g (dsnd f)) |)

total reifiable reflectable effect {
  M1 with { repr = m_repr; return = m_return; bind = m_bind }
}

let m1_big : Type u#1 = unit -> M1 bool (requires True) (ensures fun _ -> True)

(* THE BUG: this was accepted, though [M1 bool] is inhabited by a
   [(t:Type u#0 & bool)] and so cannot fit in [Type u#0]. *)
[@@expect_failure [189]]
let m1_unsound : Type u#0 = unit -> M1 bool (requires True) (ensures fun _ -> True)

(** 3. A universe-LOWERING representation: [M2 t] is in [Type u#0] however
       large [t] is, so the new rule accepts more than the old one did. *)

let k_repr (a:Type u#a) : Type u#0 = bool
let k_return (a:Type u#a) (x:a) : k_repr a = true
let k_bind (a:Type u#a) (b:Type u#b) (f:k_repr a) (g:a -> k_repr b) : k_repr b = f

total reifiable effect {
  M2 with { repr = k_repr; return = k_return; bind = k_bind }
}

let m2_small : Type u#0 = unit -> M2 (Type u#5) (requires True) (ensures fun _ -> True)

(** 4. A PARTIAL effect stays in [Type u#0] whatever its representation: an
       arrow into it is not a type of values.  [M3]'s representation is in
       [Type u#1], but [unit -> M3 t] is still [Type u#0]. *)

let d_repr (a:Type u#a) : Type u#1 = (t:Type u#0 & (unit -> Dv a))
let d_return (a:Type u#a) (x:a) : d_repr a = (| unit, (fun () -> x) |)
let d_bind (a:Type u#a) (b:Type u#b) (f:d_repr a) (g:a -> d_repr b) : d_repr b =
  (| dfst f, (fun () -> let x = dsnd f () in dsnd (g x) ()) |)

reifiable effect { M3 with { repr = d_repr; return = d_return; bind = d_bind } }

let m3_small : Type u#0 = unit -> M3 (Type u#5) (requires True) (ensures fun _ -> True)

(** 5. [Tot] and [GTot] have no representation to consult, and must keep
       answering with the universe of the result type. *)

let tot_small : Type u#0 = unit -> bool
let tot_big   : Type u#1 = unit -> Type u#0
let gtot_big  : Type u#1 = unit -> GTot (Type u#0)

[@@expect_failure [189]]
let tot_too_small : Type u#0 = unit -> Type u#0
