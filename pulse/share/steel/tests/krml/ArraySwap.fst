module ArraySwap
open Steel.ST.Util
open Steel.ST.Array.Swap

let main () : ST Int32.t emp (fun _ -> emp) True (fun i -> i == 0l) = 
  let arr = malloc 0l 12sz in
  pts_to_length arr _;
  upd arr 1sz 1l;
  upd arr 2sz 2l;
  upd arr 3sz 3l;
  upd arr 4sz 4l;
  upd arr 5sz 5l;
  upd arr 6sz 6l;
  upd arr 7sz 7l;
  upd arr 8sz 8l;
  upd arr 9sz 9l;
  upd arr 10sz 10l;
  upd arr 11sz 11l;
  let _ = swap arr 12sz 8sz in
  let a3 = index arr 3sz in
  let a7 = index arr 7sz in
  let b = (a3 = 11l && a7 = 3l) in
  free arr;
  return (if b then 0l else 1l)
