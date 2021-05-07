module SelectorLogic

open Steel.Memory
module Mem = Steel.Memory

(* Extending selectors to support wand; establishing a correspondance with linear logic *)

#push-options "--ide_id_info_off"

let selector (hp:slprop) (a:(hmem hp) -> Type) = (h:hmem hp -> GTot (a h))

/// The basis of our selector framework: Separation logic assertions enhanced with selectors
/// Note that selectors are "optional", it is always possible to use a non-informative selector,
/// such as fun _ -> () and to rely on the standard separation logic reasoning
noeq
type vprop =
  { hp: slprop u#1;
    t:hmem hp -> Type;
    sel:selector hp t }

(* This lemma should be exposed in mem *)
assume
val reveal_wand (p q:slprop) (m:mem) : Lemma
  (requires interp (Mem.wand p q) m)
  (ensures forall m1. (m `disjoint` m1 /\ interp p m1) ==> interp q (join m m1))
  [SMTPat (interp (Mem.wand p q) m)]


let star (p q:vprop) =
  {hp = p.hp `Mem.star` q.hp;
   t = (fun h -> p.t h * q.t h);
   sel = fun h -> p.sel h, q.sel h
  }

(* Separating for clarity *)
let left_wand_t (m:mem) (p:vprop) =
  h:hmem p.hp{disjoint h m} & p.t h

let wand (p q:vprop) =
  {hp = p.hp `Mem.wand` q.hp;
   t = (fun m -> ((x:left_wand_t m p) -> GTot (q.t (join m (dfst x)))));
   sel = fun m0 -> fun (| h, vp |) -> q.sel (join m0 h)
  }

(* Simplification to avoid reasoning about existentials *)
val star_split (p q:slprop) (m:hmem (p `Mem.star` q))
  : GTot (r:(hmem p * hmem q){disjoint (fst r) (snd r) /\ join (fst r) (snd r) == m})

let star_split p q m =
  elim_star p q m;
  let ml = FStar.IndefiniteDescription.indefinite_description_ghost mem (
    fun ml -> exists mr. disjoint ml mr /\ m == join ml mr /\ interp p ml /\ interp q mr) in
  let mr = FStar.IndefiniteDescription.indefinite_description_ghost mem (
    fun mr -> disjoint ml mr /\ m == join ml mr /\ interp p ml /\ interp q mr) in
  ml, mr

let modus_ponens_interp (p q:vprop) (m:hmem (p `star` (p `wand` q)).hp)
  : Lemma (interp q.hp m)
  = let mp, mq = star_split p.hp (p `wand` q).hp m in
    assert (interp q.hp (join mq mp));
    join_commutative mq mp

let modus_ponens_derive_sel (p q:vprop)
  (m:hmem (p `star` (p `wand` q)).hp)
  (* Only used to typecheck q.t m' *)
  (m':hmem q.hp{m == m'}) : GTot (q.t m')
  = let mp, mq = star_split p.hp (p `wand` q).hp m in
    let vp = p.sel mp in
    let res:q.t (join mq mp) = (p `wand` q).sel mq (|mp, vp|) in
    join_commutative mq mp;
    res

(* One example of selector *)

open Steel.FractionalPermission
open Steel.SelReference

let ref (a:Type0) : Type0 = ref a
let ptr (#a:Type0) (r:ref a) : slprop u#1 = ptr r

let ptr_sel (#a:Type0) (r:ref a) : selector (ptr r) (fun _ -> a) = ptr_sel r

let vptr' #a r : vprop =
  {hp = ptr r;
   t = (fun _ -> a);
   sel = ptr_sel r}
