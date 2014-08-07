module PartialMap
open Prims.PURE

assume type t : Type => Type => Type

assume logic val Sel : 'k:Type -> 'v:Type -> m:t 'k 'v -> k:'k -> Tot 'v
assume logic val Upd : 'k:Type -> 'v:Type -> m:t 'k 'v -> k:'k -> v:'v -> Tot (t 'k 'v)
assume logic val Emp : 'k:Type -> 'v:Type -> Tot (t 'k 'v)
assume logic val Concat: 'k:Type -> 'v:Type -> t 'k 'v -> t 'k 'v -> Tot (t 'k 'v)
assume logic val ConstMap: 'k:Type -> 'v:Type -> set 'k -> 'v -> Tot (t 'k 'v)
logic type InDom  : #'k:Type => #'v:Type => 'k => t 'k 'v => Type
type DisjointDom : #'k:Type => #'v:Type => t 'k 'v => t 'k 'v => Type = 
    fun 'k 'v (m1:t 'k 'v) (m2:t 'k 'v) => (forall x. InDom x m1 ==> ~(InDom x m2))
                         
assume SelUpd1: forall ('k:Type) ('v:Type) (m:t 'k 'v) (k:'k) (v:'v).{:pattern (Sel (Upd m k v) k)} Sel (Upd m k v) k == k
assume SelUpd2: forall ('k:Type) ('v:Type) (m:t 'k 'v) (k1:'k) (k2:'k) (v:'v).{:pattern (Sel (Upd m k2 v) k1)} k2=!=k1 ==> Sel (Upd m k2 v) k1 == Sel m k1
(* assume InDomEmp:   forall ('k:Type) ('v:Type) (kk:'k).{:pattern InDom 'k 'v kk (Emp 'k 'v)} ~(InDom 'k 'v kk (Emp 'k 'v)) *)
assume InDom1:     forall ('k:Type) ('v:Type) (m:t 'k 'v) (k:'k) (v:'v).{:pattern InDom k (Upd m k v)} InDom k (Upd m k v)
assume InDom2:     forall ('k:Type) ('v:Type) (m:t 'k 'v) (k1:'k) (k2:'k) (v:'v).{:pattern InDom k1 (Upd m k2 v)} (k2=!=k1 /\ InDom k1 m) ==> InDom k1 (Upd m k2 v)
assume SelConcat1: forall ('k:Type) ('v:Type) (m1:t 'k 'v) (m2:t 'k 'v) (k:'k).{:pattern Sel (Concat m1 m2) k} InDom k m2 ==> Sel (Concat m1 m2) k==Sel m2 k
assume SelConcat1: forall ('k:Type) ('v:Type) (m1:t 'k 'v) (m2:t 'k 'v) (k:'k).{:pattern Sel (Concat m1 m2) k} ~(InDom k m2) ==> Sel (Concat m1 m2) k==Sel m1 k

