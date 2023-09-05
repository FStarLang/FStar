module Pulse.Typing.Env

open FStar.List.Tot

open Pulse.Syntax

module L = FStar.List.Tot

module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2

type binding = var & typ
type env_bindings = list binding

val env : Type0

val fstar_env (g:env) : RT.fstar_top_env

//
// most recent binding at the head of the list
//
val bindings (g:env) : env_bindings

val as_map (g:env) : Map.t var typ

let is_related_to (bs:list (var & typ)) (m:Map.t var typ) =
  (forall (b:var & typ).{:pattern L.memP b bs}
          L.memP b bs ==> (Map.contains m (fst b) /\
                           Map.sel m (fst b) == snd b)) /\
  
  (forall (x:var).{:pattern Map.contains m x} Map.contains m x ==> (L.memP (x, Map.sel m x) bs))

val bindings_as_map (g:env)
  : Lemma (bindings g `is_related_to` as_map g)
          [SMTPat (bindings g); SMTPat (as_map g)]

let dom (g:env) : Set.set var = Map.domain (as_map g)

let equal (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  bindings g1 == bindings g2

val equal_elim (g1 g2:env)
  : Lemma (requires equal g1 g2)
          (ensures g1 == g2)
          [SMTPat (equal g1 g2)]

val mk_env (f:RT.fstar_top_env) : g:env { fstar_env g == f }

val mk_env_bs (f:RT.fstar_top_env)
  : Lemma (bindings (mk_env f) == [])
          [SMTPat (bindings (mk_env f))]

val mk_env_dom (f:RT.fstar_top_env)
  : Lemma (dom (mk_env f) == Set.empty)
          [SMTPat (dom (mk_env f))]

val push_binding (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : g':env { fstar_env g' == fstar_env g }

let singleton_env (f:_) (x:var) (t:typ) = push_binding (mk_env f) x ppname_default t

let push_binding_def (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  = push_binding g x ppname_default t

val push_binding_bs (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (bindings (push_binding g x n t) == (x, t) :: bindings g)
          [SMTPat (bindings (push_binding g x n t))]

val push_binding_as_map (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (as_map (push_binding g x n t) == Map.upd (as_map g) x t)
          [SMTPat (as_map (push_binding g x n t))]

let lookup (g:env) (x:var) : option typ =
  let m = as_map g in
  if Map.contains m x then Some (Map.sel m x) else None

val fresh (g:env) : v:var { ~ (Set.mem v (dom g)) }

let contains (g:env) (x:var) = Map.contains (as_map g) x

let disjoint (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  Set.disjoint (dom g1) (dom g2)

let pairwise_disjoint (g g' g'':env) =
  disjoint g g' /\ disjoint g' g'' /\ disjoint g g''

let disjoint_dom (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures dom g1 `Set.disjoint` dom g2) = ()

val push_env (g1:env) (g2:env { disjoint g1 g2 }) : env

val push_env_fstar_env (g1:env) (g2:env { disjoint g1 g2 })
  : Lemma (fstar_env (push_env g1 g2) == fstar_env g1)
          [SMTPat (fstar_env (push_env g1 g2))]

val push_env_bindings (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures bindings (push_env g1 g2) == bindings g2 @ bindings g1)
          [SMTPat (bindings (push_env g1 g2))]

val push_env_as_map (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures as_map (push_env g1 g2) == Map.concat (as_map g2) (as_map g1))
          [SMTPat (as_map (push_env g1 g2))]

val push_env_assoc (g1 g2 g3:env)
  : Lemma (requires disjoint g1 g2 /\ disjoint g2 g3 /\ disjoint g3 g1)
          (ensures push_env g1 (push_env g2 g3) == push_env (push_env g1 g2) g3)

val check_disjoint (g:env) (s:Set.set var) : b:bool { b ==> Set.disjoint s (dom g)}

// removes the binding that was added first
// leftmost when we write env on paper
val remove_binding (g:env { Cons? (bindings g) })
  : Pure (var & typ & env)
         (requires True)
         (ensures fun r ->
            let (x, t, g') = r in
            fstar_env g' == fstar_env g /\
            (~ (x `Set.mem` dom g')) /\
            g == push_env (push_binding (mk_env (fstar_env g)) x ppname_default t) g')

val remove_latest_binding (g:env { Cons? (bindings g) })
  : Pure (var & typ & env)
         (requires True)
         (ensures fun r ->
            let (x, t, g') = r in
            fstar_env g' == fstar_env g /\
            (~ (x `Set.mem` dom g')) /\
            g == push_binding g' x ppname_default t)

// g1 extends g2 with g3, i.e. g1.bs == g3.bs @ g2.bs (recall most recent binding at the head)
let extends_with (g1 g2 g3:env) =
  disjoint g2 g3 /\
  g1 == push_env g2 g3

let env_extends (g1 g2:env) =
  exists g3. extends_with g1 g2 g3

val diff (g1 g2:env)
  : Pure env (requires g1 `env_extends` g2)
             (ensures fun g3 -> extends_with g1 g2 g3)

val env_extends_refl (g:env)
  : Lemma (g `env_extends` g)
          [SMTPat (g `env_extends` g)]

val env_extends_trans (g1 g2 g3:env)
  : Lemma (requires g1 `env_extends` g2 /\ g2 `env_extends` g3)
          (ensures g1 `env_extends` g3)
          [SMTPat (g1 `env_extends` g3); SMTPat (g1 `env_extends` g2)]

val env_extends_push (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (push_binding g x n t `env_extends` g)
          [SMTPat ((push_binding g x n t) `env_extends` g)]

val extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) (n:ppname) (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x n t) g2 (push_binding g3 x n t))
          [SMTPat (extends_with g1 g2 g3);
           SMTPat (push_binding g1 x n t);
           SMTPat (push_binding g3 x n t)]

val subst_env (en:env) (ss:subst)
  : en':env { fstar_env en == fstar_env en' /\
              dom en == dom en' }

val push_context (g:env) (ctx:string) (r:range) : g':env { g' == g }
val push_context_no_range (g:env) (ctx:string) : g':env { g' == g }
val get_context (g:env) : Pulse.RuntimeUtils.context
val range_of_env (g:env) : T.Tac range
val print_context (g:env) : T.Tac string
val print_issue (g:env) (i:FStar.Issue.issue) : T.Tac string 
val print_issues (g:env) (i:list FStar.Issue.issue) : T.Tac string
val env_to_string (g:env) : T.Tac string
val get_range (g:env) (r:option range) : T.Tac range
val fail (#a:Type) (g:env) (r:option range) (msg:string) 
  : T.TAC a (fun _ post -> forall ex ps. post FStar.Tactics.Result.(Failed ex ps))

val warn (g:env) (r:option range) (msg:string)
  : T.Tac unit

val info (g:env) (r:option range) (msg:string)
  : T.Tac unit
