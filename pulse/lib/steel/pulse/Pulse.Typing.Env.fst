module Pulse.Typing.Env

open Pulse.Syntax

module L = FStar.List.Tot

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

open FStar.List.Tot

type bmap = m:Map.t var typ {
  forall (x:var). (~ (Map.contains m x)) ==> (Map.sel m x == Tm_Unknown)
}

let remove_binding ((x, _):var & typ) (m:bmap) : bmap =
  Map.restrict (Set.complement (Set.singleton x)) (Map.upd m x Tm_Unknown)

let related (bs:list (var & typ)) (m:Map.t var typ) =
  (forall (b:var & typ).
          L.memP b bs ==> (Map.contains m (fst b) /\
                           Map.sel m (fst b) == snd b)) /\
  
  (forall (x:var). Map.contains m x ==> (List.Tot.memP (x, Map.sel m x) bs))

noeq
type env = {
  f : RT.fstar_top_env;
  bs : list (var & typ);
  m : m:bmap { related bs m };
  ctxt: Pulse.RuntimeUtils.context
}

let fstar_env g = g.f

let bindings g = g.bs

let as_map g = g.m

let bindings_as_map _ = ()

let empty_bmap : bmap = Map.const_on Set.empty Tm_Unknown

let mk_env (f:RT.fstar_top_env) : env = { f; bs = []; m = empty_bmap; ctxt = FStar.Sealed.seal [] }

let mk_env_bs _ = ()

let push_binding g x t =
  { g with bs = (x, t)::g.bs; m = Map.upd g.m x t }

let push_binding_bs _ _ _ = ()

let push_binding_as_map _ _ _ = ()

let rec max (bs:list (var & typ)) (current:var)
  : v:var { current <= v /\ (forall (b:var & typ). List.Tot.memP b bs ==> fst b <= v) } =
  match bs with
  | [] -> current
  | (x, t)::rest ->
    let current = if x < current then current else x in
    max rest current

let fresh g =
  match g.bs with
  | [] -> 1
  | (x, _)::bs_rest ->
    let max = max bs_rest x in
    max + 1

//
// TODO: Move to ulib
//
let rec append_memP (#a:Type) (l1 l2:list a) (x:a)
  : Lemma (L.memP x (l1 @ l2) <==> (L.memP x l1 \/ L.memP x l2))
          [SMTPat (L.memP x (l1 @ l2))] =
  match l1 with
  | [] -> ()
  | _::tl -> append_memP tl l2 x

let join (g1:env) (g2:env { disjoint g1 g2 }) : env =
  { f = g1.f; bs = g1.bs @ g2.bs; m = Map.concat g1.m g2.m; ctxt = FStar.Sealed.seal [] }

let intro_env_extends (g1 g2 g3:env)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures g1 `env_extends` g2) = ()

let elim_env_extends (g1:env) (g2:env { g1 `env_extends` g2 })
  : GTot (g3:env { extends_with g1 g2 g3 }) =
  FStar.IndefiniteDescription.indefinite_description_ghost
    env (fun g3 -> extends_with g1 g2 g3)

let env_extends_refl (g:env) : Lemma (g `env_extends` g) =
  intro_env_extends g g (mk_env g.f)

let env_extends_trans (g1 g2 g3:env)
  : Lemma (requires g1 `env_extends` g2 /\ g2 `env_extends` g3)
          (ensures g1 `env_extends` g3) =
  let g12 = elim_env_extends g1 g2 in
  let g23 = elim_env_extends g2 g3 in
  L.append_assoc g12.bs g23.bs g3.bs;
  intro_env_extends g1 g3 (join g12 g23)

let env_extends_push (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  : Lemma (push_binding g x t `env_extends` g) =
  intro_env_extends (push_binding g x t) g (push_binding (mk_env g.f) x t)

let extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x t) g2 (push_binding g3 x t)) =
  ()

let push_context g ctx = { g with ctxt = Pulse.RuntimeUtils.extend_context ctx g.ctxt }

let get_context g = g.ctxt

