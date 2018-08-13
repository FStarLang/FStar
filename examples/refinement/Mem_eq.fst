module Mem_eq

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer



val g_upd_preserves_live : #a:Type -> h:mem -> b1:pointer a{live h b1} -> b2:pointer a{live h b2} -> v:a ->
    Lemma (let h' = g_upd b1 0 v h in modifies (loc_buffer b1) h h' /\ live h' b1 /\ live h' b2)
                                 
let g_upd_preserves_live #a h b1 b2 v = 
    let p = g_upd_seq_as_seq b1 (Seq.upd (as_seq h b1) 0 v) h in ()

// val g_upd_p : #a:Type -> h:mem -> b:pointer a{live h b} -> v:a -> GTot (h':mem{live h' b})
// let g_upd_p #a b v h = 
//     let p = g_upd_preserves_live h b b v in 
//     g_upd b 0 v h


val get_upd_eq : #a:Type -> h:mem -> b:pointer a{live h b} -> i:nat{i < length b} -> v:a ->
    Lemma (requires (get h b i == v))
          (ensures (g_upd b i v h == h))
let get_upd_eq #a h i b v = admit ()


val upd_upd_eq : #a:Type -> h:mem -> b:pointer a{live h b} -> i:nat{i < length b} -> v1:a -> v2:a ->
    Lemma (let h' = g_upd b i v1 h in
           let p = g_upd_preserves_live h b b v1 in
           g_upd b i v2 h' == g_upd b i v1 h)
let upd_upd_eq #a h i b v1 v2 = admit ()


val get_upd_same : #a:Type -> h:mem -> b1:pointer a{live h b1} -> v1:a ->
    Lemma (get (g_upd b1 0 v1 h) b1 0 == v1)
let get_upd_same #a h b1 v1 = admit ()



val get_upd_other : #a:Type -> h:mem -> b1:pointer a{live h b1} -> b2:pointer a{live h b2} -> 
    v1:a -> v2:a ->
    Lemma (requires (get h b2 0 == v2 /\ disjoint b1 b2))
          (ensures (get (g_upd b1 0 v1 h) b2 0 == v2))
let get_upd_other #a h b1 b2 v1 v2 = admit ()



