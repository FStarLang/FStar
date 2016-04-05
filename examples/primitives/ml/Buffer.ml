
let disjoint_only_lemma t b t' b' = ()  
let eq_lemma h0 h1 size a mods = ()
let modifies_transitivity_lemma mods h0 h1 h2 = ()
let modifies_subset_lemma mods submods h0 h1 = ()
let modifies_empty_lemma h = ()
let modifies_fresh_lemma h0 h1 mods size b = ()

type 'a buffer = {
    content:'a array;
    idx:int;
    length:int;
  }
                
type uint32 = int

let create t init len = {content = Array.make len init; idx = 0; length = len}
let index t b n = Array.get b.content (n+b.idx)
let upd t b n v = Array.set b.content (n+b.idx) v
let sub t b i len = {content = b.content; idx = b.idx+i; length = len}
let blit t a idx_a b idx_b len = Array.blit a.content (idx_a+a.idx) b.content (idx_b+b.idx) len
let split t a i = (sub t a 0 i, sub t a i (a.length - i))
let of_seq t s l = ()
let copy t b l = {content = Array.sub b.content b.idx l; idx = 0; length = l} 
                
