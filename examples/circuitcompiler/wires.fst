module Wires

(* TODO: ranges are wire bundles and that usually correspond to values;
take advantage of that correspondence somehow? *)
type wrange = p:(nat * nat){snd p >= fst p}

let wirezero:nat = 0
let wireone:nat = 1

let g_init = 1 (* initial counter *)
val alloc_wrange: g:nat -> sz:nat{sz > 0} -> Tot(g':nat{g' = g+sz} * wrange)
let alloc_wrange g sz = g+sz, (g+1,g+sz)

(* TODO: We convert to lists here so we can fold. But it might be
better to write iterator functions over ranges directly? *)
val rangetolist: p:wrange -> Tot (list nat) (decreases(snd p - fst p))
let rec rangetolist (i,j) =
  if j = i then [i]
  else
    i::(rangetolist (i+1,j))

val rsize: wrange -> Tot nat
let rsize (i,j) = j-i+1
