module Refinement.Generic.Fib

open Refinement.Generic
open Refinement.Generic.InstPair

(* Purely functional spec *)
let rec fib (n : int) : Tot nat (decreases n) = 
  if n <= 0 then 0
  else if n = 1 then 1
  else 
    let f1 : nat = fib (n - 1) in
    let f2 : nat = fib (n - 2) in 
    f1 + f2
  
let loop_inv (i : int) (s : nat * nat) = 
  i >= 1 /\ (fst s = fib (i - 1)) /\ (snd s = fib i) 


let shift (r:rlens l) (i : int) : 
  RST unit r (requires (loop_inv i))
             (ensures (fun s0 _ s1 -> loop_inv (i + 1) s1)) =
  let v0 = read_fst r in 
  let v1 = read_snd r in 
  set_fst r v1; 
  set_snd r (v0 + v1)


(* for combinator. TODO check if there's already one in ST *)
let rec for #roots (#invt:inv_t roots) #b (#l:lens inv b) (r: rlens l)
            (inv:int -> b -> Type0)
            (f:(i:int) -> RST unit r (inv i) (fun s0 _ s1 -> inv (i+1) s1)) 
            (lo:int) (hi:int) :
RST unit r (inv lo) (fun s0 _ s1 -> inv hi s1) (decreases (hi - lo)) = 
  if (lo = hi) then () 
  else 
    begin
      f lo; for #roots #invt #b #l r inv f (lo + 1) hi
    end 

let fib_fast (r:rlens l) n : RST int r (requires (fun _ -> True))
                                     (ensures (fun _ r _ -> r = fib n)) =
  if (n <= 0) then 0 
  else 
    begin 
      set_fst r 0;
      set_snd r 1;
      for #roots #inv #(nat * nat) #l r loop_inv (shift r) 1 n;
      read_snd r
    end
