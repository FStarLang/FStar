(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Tactics.CanonCommSwaps

open FStar.List.Tot.Base

let swap (n:nat) :Type = x:nat{x < n-1}

let rec apply_swap_aux (#a:Type) (n:nat) (xs:list a) (s:swap (length xs + n)) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases xs) =
  match xs with
  | [] | [_] -> xs
  | x1 :: x2 :: xs' -> if n = (s <: nat)
                       then x2 :: x1 :: xs'
                       else x1 :: apply_swap_aux (n+1) (x2 :: xs') s

let apply_swap (#a:Type) = apply_swap_aux #a 0

let rec apply_swaps (#a:Type) (xs:list a) (ss:list (swap (length xs))) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases ss) =
  match ss with
  | [] -> xs
  | s::ss' -> apply_swaps (apply_swap xs s) ss'

let equal_counts (#a:eqtype) (xs ys:list a) : Type0 =
  (forall (e:a).{:pattern (count e xs) \/ (count e ys)} count e xs == count e ys)

let extend_equal_counts (#a:eqtype) (h:a) (xs ys:list a) : Lemma
  (requires equal_counts xs ys)
  (ensures equal_counts (h::xs) (h::ys))
  =
  ()

let retract_equal_counts (#a:eqtype) (h:a) (xs ys:list a) : Lemma
  (requires equal_counts (h::xs) (h::ys))
  (ensures equal_counts xs ys)
  =
  assert (forall (e:a).{:pattern (count e xs) \/ (count e ys)} count e (h::xs) == count e (h::ys))

unfold let swap_for (#a:eqtype) (xs:list a) = swap (length xs)
unfold let swaps_for (#a:eqtype) (xs:list a) = list (swap_for xs)

let rec append_swaps (#a:eqtype) (xs:list a) (ss1 ss2:swaps_for xs) : Lemma
  (ensures apply_swaps xs (ss1 @ ss2) == apply_swaps (apply_swaps xs ss1) ss2)
  (decreases ss1)
  =
  match ss1 with
  | [] -> ()
  | h::t -> append_swaps (apply_swap xs h) t ss2

let rec lift_swap_cons (#a:eqtype) (n:nat) (h:a) (xs:list a) (s:swap (length xs + n)) : Lemma
  (requires n <= s)
  (ensures apply_swap_aux n (h::xs) (s + 1) == h::(apply_swap_aux n xs s))
  (decreases xs)
  =
  match xs with
  | [] -> ()
  | x::xt -> if n < s then lift_swap_cons (n + 1) x xt s

let rec lift_swaps_cons (#a:eqtype) (h:a) (xs:list a) (ss:swaps_for xs) : Pure (swaps_for (h::xs))
  (requires True)
  (ensures (fun ss' ->
    apply_swaps (h::xs) ss' == h::(apply_swaps xs ss)
  ))
  (decreases ss)
  =
  match ss with
  | [] -> []
  | s::st ->
    (
      lift_swap_cons 0 h xs s;
      (s + 1)::(lift_swaps_cons h (apply_swap xs s) st)
    )

let rec swap_to_front (#a:eqtype) (h:a) (xs:list a) : Pure (swaps_for xs)
  (requires count h xs >= 1)
  (ensures (fun ss ->
    let ys = apply_swaps xs ss in
    equal_counts xs ys /\
    Cons? ys /\
    hd ys == h
  ))
  =
  match xs with
  | [] -> []
  | x::xt ->
    (
      if x = h then []
      else
      (
        let ss = swap_to_front h xt in // ss turns xt into h::xt'
        let ss' = lift_swaps_cons x xt ss in // ss' turns x::xt into x::h::xt'
        let s:swap_for xs = 0 in
        append_swaps xs ss' [s];
        ss' @ [s]
      )
    )

let rec equal_counts_implies_swaps (#a:eqtype) (xs ys:list a) : Pure (swaps_for xs)
  (requires equal_counts xs ys)
  (ensures (fun ss -> ys == apply_swaps xs ss))
  (decreases ys)
  =
  match ys with
  | [] ->
    (
      match xs with
      | [] -> []
      | x::xt ->
        (
          assert (count x xs >= 1);
          []
        )
    )
  | y::yt ->
    (
      assert (count y ys >= 1);
      assert (count y xs >= 1);
      let ss0 = swap_to_front y xs in               // find y in xs, swap it to the front
      let xs' = apply_swaps xs ss0 in               // hd xs' == y
      let xt = tl xs' in                            // xs' == y::xt
      retract_equal_counts y xt yt;                 // prove (equal_counts xt yt)
      let ss1 = equal_counts_implies_swaps xt yt in // prove (yt == apply_swaps xt ss1)
      let ss1' = lift_swaps_cons y xt ss1 in        // y::yt == apply_swaps (y::xt) ss1'
      // ys == apply_swaps (apply_swaps xs ss0) ss1'
      append_swaps xs ss0 ss1';
      ss0 @ ss1'
    )

