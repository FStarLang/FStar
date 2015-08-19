module NormTake3

open StlcStrongDbParSubst
open Constructive

kind Relation (a:Type) = a -> a -> Type

type multi (a:Type) (r:Relation a) : a -> a -> Type =
  | Multi_refl : x:a -> multi a r x x
  | Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z

type steps : exp -> exp -> Type = multi exp step

type halts (e:exp) : Type = cexists (fun e' -> u:(steps e e'){is_value e'})

(* This has a negative occurrence of R that makes Coq and F* succumb,
   although this definition is just fine (the type decreases).  While
   in Coq we could define this as a fixpoint, we don't currently have
   type-level fixpoints in F*. *)
type red : typ -> exp -> Type =
(*  | R_bool : e:exp -> typing empty e TBool -> halts e -> red TBool e *)
  | R_arrow : t1:typ ->
              t2:typ ->
              #e:exp ->
              typing empty e (TArr t1 t2) ->
              halts e ->
              (e':exp -> red t1 e' -> Tot (red t2 (EApp e e'))) ->
              red (TArr t1 t2) e
(*
  | R_pair : t1:typ ->
             t2:typ ->
             e:exp{typing empty e (TPair t1 t2) ->
             halts e ->
             red t1 (EFst e) ->
             red t2 (ESnd e) ->
             red (TPair t1 t2) e
*)

val red_halts : t:typ -> e:exp -> red t e -> Tot (halts e)
let red_halts t e h =
  match h with
  | R_arrow _ _ _ hh _ -> hh

val red_typing : t:typ -> e:exp -> red t e -> Tot (typing empty e t)
let red_typing t e h =
  match h with
  | R_arrow k1 k2 ht k3 k4 -> ht
