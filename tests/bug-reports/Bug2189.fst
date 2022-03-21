module Bug2189

module L = FStar.List.Tot

open FStar.Tactics


[@@ strict_on_arguments [1]]
let index (#a:Type) : l:list a -> i:nat{i < L.length l} -> Tot a = 
  L.index #a

let norm () : Tac unit =
  norm [delta_only [
         `%L.hd;
         `%L.tl;
         `%L.tail;
         `%L.index;
         `%index]; iota; zeta; primops];
  trefl ()

[@@ postprocess_with norm]
unfold
let x = index ([0;1;2]) 2

[@@ postprocess_with norm]
unfold
let y = index ([0;1;2] <: list int) 2

#set-options "--no_smt"
let test () =
  assert (x == 2);
  assert (y == 2)
