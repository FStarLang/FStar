module Mem_eq

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer


val get_upd_eq : #a:Type -> h:mem -> b:buffer a{live h b} -> i:nat{i < length b} -> v:a ->
    Lemma (requires (get h b i == v))
          (ensures (g_upd b i v h == h))

let get_upd_eq #a h i b v = admit ()







