module Pulse.Common

module L = FStar.List.Tot
open FStar.Tactics

let (let?) (f:option 'a) (g:'a -> option 'b) : option 'b =
  match f with
  | None -> None
  | Some x -> g x

// let lem_bind_opt_some (x : option 'a) (f : 'a -> option 'b)
//   : Lemma (requires Some? ((let?) x f))
//           (ensures Some? x /\ Some? (f (Some?.v x)))
//           [SMTPat (Some? ((let?) x f))]
//   = ()

// let lem_bind_opt_none (x : option 'a) (f : 'a -> option 'b)
//   : Lemma (requires None? ((let?) x f))
//           (ensures None? x \/ None? (f (Some?.v x)))
//           [SMTPat (Some? ((let?) x f))]
//   = ()

let rec for_all_dec (top:'a) (f : (x:'b{x << top} -> bool)) (l : list 'b{l << top}) : bool =
  match l with
  | [] -> true
  | x::xs -> f x && for_all_dec top f xs

let rec map_dec (top:'a) (l : list 'b{l << top}) (f : (x:'b{x << l} -> 'c)) : list 'c =
  match l with
  | [] -> []
  | x::xs -> f x :: map_dec top xs f

let rec zipWith (f : 'a -> 'b -> Tac 'c) (l : list 'a) (m : list 'b)
  : Tac (l':(list 'c){L.length l' == min (L.length l) (L.length m)})
  =
  match l, m with
  | [], [] -> []
  | x::xs, y::ys -> f x y :: zipWith f xs ys
  | _ -> fail "zipWith: length mismatch"
  
val zip : (#a:Type) -> (#b:Type) -> l1:list a -> l2:list b ->
  Tot (l:list (a * b){L.length l == min (L.length l1) (L.length l2)})
let rec zip #a #b l1 l2 = match l1, l2 with
    | x::xs, y::ys -> (x,y) :: (zip xs ys)
    | _ -> []

let rec map_opt f l = match l with
  | [] -> Some []
  | x::xs ->
    let? y = f x in
    let? ys = map_opt f xs in
    Some (y::ys)

let rec map_opt_dec #a #b #z (top:z) (f : (x:a{x << top}) -> option b) (l : list a{l << top}) : option (list b)
= match l with
  | [] -> Some []
  | x::xs ->
    let? y = f x in
    let? ys = map_opt_dec top f xs in
    Some (y::ys)

let rec concat_map_opt #a #b (f : a -> option (list b)) (l : list a) : option (list b) =
  match l with
  | [] -> Some []
  | x::xs ->
    let? y = f x in
    let? ys = concat_map_opt f xs in
    Some (y@ys)

let rec lemma_map_opt_dec_len #a #b #z (top:z) (f : (x:a{x << top}) -> option b) (xs : list a{xs << top})
  : Lemma (requires (Some? (map_opt_dec top f xs)))
          (ensures (L.length (Some?.v (map_opt_dec top f xs)) == L.length xs))
          [SMTPat (map_opt_dec top f xs)]
  = match xs with
    | [] -> ()
    | x::xs -> lemma_map_opt_dec_len top f xs

// let rec __lemma_map_opt_index (f : 'a -> option 'b) (xs : list 'a) (ys : list 'b) (i:nat{i < L.length xs})
//   : Lemma (requires map_opt f xs == Some ys)
//           (ensures f (xs `L.index` i) == Some (ys `L.index` i))
//   = match xs, ys, i with
//     | _, _, 0 -> ()
//     | x::xs, y::ys, _ ->
//      __lemma_map_opt_index f xs ys (i-1)

// let lemma_map_opt_index (f : 'a -> option 'b) (xs : list 'a) (ys : list 'b)
//   : Lemma (requires map_opt f xs == Some ys)
//           (ensures forall i. f (xs `L.index` i) == Some (ys `L.index` i))
//   = Classical.forall_intro (Classical.move_requires (__lemma_map_opt_index f xs ys))


let dec_index #a (top:'z) (l : list a{l << top}) (i : nat{i < L.length l})
: Lemma (l `L.index` i << top)
        [SMTPat (l `L.index` i << top)]
= admit()











let rec lemma_map_dec_len #a #b #z (top:z) (f : (x:a{x << top}) -> b) (xs : list a{xs << top})
  : Lemma (ensures (L.length (map_dec top xs f) == L.length xs))
          [SMTPat (map_dec top xs f)]
  = match xs with
    | [] -> ()
    | x::xs -> lemma_map_dec_len top f xs

let rec __lemma_map_dec_index (top:'z) (f : (x:'a{x<<top}-> 'b)) (xs : list 'a{xs << top}) (ys : list 'b) (i:nat{i < L.length xs})
  : Lemma (requires ys == map_dec top xs f)
          (ensures f (xs `L.index` i) == ys `L.index` i)
  = match xs, ys, i with
    | _, _, 0 -> ()
    | x::xs, y::ys, _ ->
     __lemma_map_dec_index top f xs ys (i-1)

let lemma_map_dec_index (top:'z) (f : (x:'a{x<<top}) -> 'b) (xs : list 'a{xs << top})
  : Lemma (ensures forall i. f (xs `L.index` i) == map_dec top xs f `L.index` i)
  = Classical.forall_intro (Classical.move_requires (__lemma_map_dec_index top f xs (map_dec top xs f)))

let lemma_map_dec_index_i (top:'z) (f : (x:'a{x<<top}) -> 'b) (xs : list 'a{xs << top}) (i : nat {i < L.length xs})
  : Lemma (ensures f (xs `L.index` i) == map_dec top xs f `L.index` i)
  = lemma_map_dec_index top f xs

let assertby (p:prop) (pf : unit -> Lemma p) : Lemma p =
  pf ()

// let map_dec_fusion
//     (top1:'y) (top2:'z)
//     (f : (x:'a{x<<top1}) -> 'b) (g : (x:'b{x<<top2} -> 'c))
//     (xs : list 'a{xs << top1})
//     (i : nat{i < L.length xs})
//   : Lemma (requires map_dec top1 f xs << top2)
//           (ensures map_dec top2 g (map_dec top1 f xs) `L.index` i == g (f (xs `L.index` i)))
//   = ()
