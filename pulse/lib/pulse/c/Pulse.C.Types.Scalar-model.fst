module Pulse.C.Types.Scalar
#lang-pulse

(* Model implementation of Pulse.C.Types.Scalar: verified, but never extracted.
   A scalar value is either unknown, uninitialized, or a value with a
   fractional permission. *)

open Pulse.Lib.Pervasives
friend Pulse.C.Types.Base
open Pulse.C.Types.Base

noeq
type scalar_t0 (t: Type0) : Type0 =
| SUnknown: scalar_t0 t
| SUninit: scalar_t0 t
| SValue: (v: t) -> (p: perm) -> scalar_t0 t

let scalar_t t = scalar_t0 t

let scalar_fractionable (#t: Type0) (x: scalar_t0 t) : prop =
  match x with
  | SValue _ p -> p <=. 1.0R
  | _ -> True

let scalar_mk_fraction (#t: Type0) (x: scalar_t0 t) (p: perm) : Pure (scalar_t0 t)
  (requires (scalar_fractionable x))
  (ensures (fun y -> p <=. 1.0R ==> scalar_fractionable y))
= match x with
  | SValue v q -> SValue v (q `prod_perm` p)
  | _ -> x

let scalar_full (#t: Type0) (x: scalar_t0 t) : prop =
  match x with
  | SUnknown -> False
  | SUninit -> True
  | SValue _ p -> p == 1.0R

let scalar_td (t: Type0) : typedef (scalar_t0 t) = {
  td_fractionable = scalar_fractionable;
  td_mk_fraction = scalar_mk_fraction;
  td_mk_fraction_full = (fun _ -> ());
  td_mk_fraction_compose = (fun _ _ _ -> ());
  td_full = scalar_full;
  td_uninitialized = SUninit;
  td_unknown = SUnknown;
  td_full_not_unknown = (fun _ -> ());
  td_mk_fraction_unknown = (fun _ -> ());
  td_mk_fraction_eq_unknown = (fun _ _ -> ());
}

let scalar t = scalar_td t

let mk_scalar v = SValue v 1.0R

let mk_scalar_fractionable v p = ()

let mk_scalar_inj v1 v2 p1 p2 = ()

fn read0 (#t: Type) (#v: Ghost.erased t) (#p: perm) (r: ref (scalar t))
requires pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p)
returns v': t
ensures pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p) ** pure (v' == Ghost.reveal v)
{
  unfold (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p));
  unreachable ()
}

let get_scalar_value c =
  match c with
  | SValue v _ -> Some v
  | _ -> None

let get_scalar_value_mk_fraction c p = ()

let get_scalar_value_mk_scalar c = ()

let get_scalar_value_uninitialized t = ()

let get_scalar_value_unknown t = ()

let get_scalar_value_some #t c =
  let SValue v0 p = c in
  assert (c == mk_fraction (scalar t) (mk_scalar v0) p)

fn write (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) (v': t)
requires pts_to r v ** pure (full (scalar t) v)
ensures pts_to r (mk_scalar v')
{
  unfold (pts_to r v);
  unreachable ()
}
