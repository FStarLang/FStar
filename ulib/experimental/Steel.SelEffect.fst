module Steel.SelEffect

module Sem = Steel.Semantics.Hoare.MST
open Steel.Memory
open Steel.Semantics.Instantiate
open Steel.Effect.Common
module FExt = FStar.FunctionalExtensionality

let selector' (a:Type) (hp:slprop) = hmem hp -> a

let sel_depends_only_on (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp) (m1:mem{disjoint m0 m1}).
    (interp_depends_only_on hp;
    sel m0 == sel (join m0 m1))

let selector (a:Type) (hp:slprop) : Type = sel:selector' a hp{sel_depends_only_on sel}

noeq
type vprop =
  { hp: slprop u#1;
    t:Type;
    sel: selector t hp}

type pre_t = vprop
type post_t (a:Type) = a -> vprop

let can_be_split (p q:vprop) = can_be_split p.hp q.hp


let rmem (pre:pre_t) = FExt.restricted_t (r0:vprop{can_be_split pre r0}) (fun r0 -> r0.t)

unfold
let unrestricted_mk_rmem (r:vprop) (h:hmem r.hp) = fun (r0:vprop{r `can_be_split` r0}) -> r0.sel h

val mk_rmem (r:vprop) (h:hmem r.hp) : Tot (rmem r)

let mk_rmem r h =
   FExt.on_dom
     (r0:vprop{r `can_be_split` r0})
     (unrestricted_mk_rmem r h)

let reveal_mk_rmem (r:vprop) (h:hmem r.hp) (r0:vprop{r `can_be_split` r0})
  : Lemma ((mk_rmem r h) r0 == r0.sel h)
  = FExt.feq_on_domain (unrestricted_mk_rmem r h)

type req_t (pre:pre_t) = rmem pre -> prop
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  rmem pre -> (x:a) -> rmem (post x) -> prop

let rmem_depends_only_on' (pre:pre_t) (m0:hmem pre.hp) (m1:mem{disjoint m0 m1})
  : Lemma (mk_rmem pre m0 == mk_rmem pre (join m0 m1))
  = Classical.forall_intro (reveal_mk_rmem pre m0);
    Classical.forall_intro (reveal_mk_rmem pre (join m0 m1));
    FExt.extensionality
      (r0:vprop{can_be_split pre r0})
      (fun r0 -> r0.t)
      (mk_rmem pre m0)
      (mk_rmem pre (join m0 m1))

let rmem_depends_only_on (pre:pre_t)
  : Lemma (forall (m0:hmem pre.hp) (m1:mem{disjoint m0 m1}).
    mk_rmem pre m0 == mk_rmem pre (join m0 m1))
  = Classical.forall_intro_2 (rmem_depends_only_on' pre)

let rmem_depends_only_on_post' (#a:Type) (post:post_t a)
    (x:a) (m0:hmem (post x).hp) (m1:mem{disjoint m0 m1})
  : Lemma (mk_rmem (post x) m0 == mk_rmem (post x) (join m0 m1))
  = rmem_depends_only_on' (post x) m0 m1

let rmem_depends_only_on_post (#a:Type) (post:post_t a)
  : Lemma (forall (x:a) (m0:hmem (post x).hp) (m1:mem{disjoint m0 m1}).
    mk_rmem (post x) m0 == mk_rmem (post x) (join m0 m1))
  = Classical.forall_intro_3 (rmem_depends_only_on_post' post)

let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state pre.hp =
  rmem_depends_only_on pre;
  fun m0 -> interp pre.hp m0 /\ req (mk_rmem pre m0)

unfold
let to_post (#a:Type) (post:post_t a) = fun x -> (post x).hp

let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a pre.hp (to_post post)
= rmem_depends_only_on pre;
  rmem_depends_only_on_post post;
  fun m0 x m1 ->
    interp pre.hp m0 /\ interp (post x).hp m1 /\ ens (mk_rmem pre m0) x (mk_rmem (post x) m1)


val repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

let repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a (pre.hp) (to_post post) (req_to_act_req req) (ens_to_act_ens ens)
