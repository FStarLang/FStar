module Pulse.Typing.Env

open FStar.List.Tot

open Pulse.Syntax

module L = FStar.List.Tot

module RT = FStar.Reflection.Typing

val env : Type0

val fstar_env (g:env) : RT.fstar_top_env

type binding = var & typ
type env_bindings = list binding

//
// most recent binding at the head of the list
//
val bindings (g:env) : env_bindings

val as_map (g:env) : Map.t var typ

let is_related_to (bs:list (var & typ)) (m:Map.t var typ) =
  (forall (b:var & typ).
          L.memP b bs ==> (Map.contains m (fst b) /\
                           Map.sel m (fst b) == snd b)) /\
  
  (forall (x:var). Map.contains m x ==> (L.memP (x, Map.sel m x) bs))

val bindings_as_map (g:env)
  : Lemma (bindings g `is_related_to` as_map g)
          [SMTPat (bindings g); SMTPat (as_map g)]

let dom (g:env) : Set.set var = Map.domain (as_map g)

val mk_env (f:RT.fstar_top_env) : g:env { fstar_env g == f }

val mk_env_bs (f:RT.fstar_top_env)
  : Lemma (bindings (mk_env f) == [])
          [SMTPat (bindings (mk_env f))]

val push_binding (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  : g':env { fstar_env g' == fstar_env g }

val push_binding_bs (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  : Lemma (bindings (push_binding g x t) == (x, t) :: bindings g)
          [SMTPat (bindings (push_binding g x t))]

val push_binding_as_map (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  : Lemma (as_map (push_binding g x t) == Map.upd (as_map g) x t)
          [SMTPat (as_map (push_binding g x t))]

let lookup (g:env) (x:var) : option typ =
  let m = as_map g in
  if Map.contains m x then Some (Map.sel m x) else None

val fresh (g:env) : v:var { ~ (Set.mem v (dom g)) }

let contains (g:env) (x:var) = Map.contains (as_map g) x

let disjoint (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  Set.disjoint (dom g1) (dom g2)

// g1 extends g2 with g3, i.e. g1.bs == g3.bs @ g2.bs (recall most recent binding at the head)
let extends_with (g1 g2 g3:env) =
  disjoint g2 g3 /\
  fstar_env g1 == fstar_env g2 /\
  bindings g1 == bindings g3 @ bindings g2 /\
  Map.equal (as_map g1) (Map.concat (as_map g3) (as_map g2))

let env_extends (g1 g2:env) =
  exists g3. extends_with g1 g2 g3

val env_extends_refl (g:env)
  : Lemma (g `env_extends` g)
          [SMTPat (g `env_extends` g)]

val env_extends_trans (g1 g2 g3:env)
  : Lemma (requires g1 `env_extends` g2 /\ g2 `env_extends` g3)
          (ensures g1 `env_extends` g3)
          [SMTPat (g1 `env_extends` g3); SMTPat (g1 `env_extends` g2)]

val env_extends_push (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  : Lemma (push_binding g x t `env_extends` g)
          [SMTPat (push_binding g x t)]

val extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x t) g2 (push_binding g3 x t))
          [SMTPat (extends_with g1 g2 g3);
           SMTPat (push_binding g1 x t);
           SMTPat (push_binding g3 x t)]

val push_context (g:env) (ctx:string) : g':env { g' == g }

val get_context (g:env) : Pulse.RuntimeUtils.context
