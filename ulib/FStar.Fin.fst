module FStar.Fin

(* This module is supposed to contain various lemmas about finiteness : *)
(* pigeonhole principle, cardinality, relation with injections and surjections... *)

module L = FStar.List.Tot
module S = FStar.Seq

let fin (n: nat) = k: int{0 <= k /\ k < n}

let vect (n: nat) (a: Type) = l: list a {L.length l = n}

let seqn (n: nat) (a: Type) = s: S.seq a {S.length s = n}

let in_ (#a: Type) (s: S.seq a) = n: nat{n < S.length s}

let rec find (#a: Type) (s: S.seq a) (p: (a -> bool)) (i: nat{i < S.length s})
  : Pure (option (j: nat{j < S.length s}))
    (requires True)
    (ensures
      (function
        | None -> (forall (k: nat{i <= k /\ k < S.length s}). p (S.index s k) == false)
        | Some j -> i <= j /\ p (S.index s j)))
    (decreases (S.length s - i)) =
  if p (S.index s i) then Some i else if i + 1 < S.length s then find #a s p (i + 1) else None

let rec pigeonhole (#n: nat) (s: S.seq (fin n))
  : Pure (in_ s * in_ s)
    (requires (b2t (S.length s = n + 1)))
    (ensures (fun (i1, i2) -> i1 < i2 /\ S.index s i1 = S.index s i2))
    (decreases n) =
  if n = 0
  then (match S.index s 0 with )
  else
    if n = 1
    then
      (assert (S.index s 0 = S.index s 1);
        0, 1)
    else
      let k0 = S.index s 0 in
      match find s (fun k -> k = k0) 1 with
      | Some i -> 0, i
      | None ->
        let reduced_s: S.seq (fin (n - 1)) =
          S.init #(fin (n - 1))
            n
            (fun i ->
                let k: nat = S.index s (i + 1) in
                assert (k <> k0);
                if k < k0 then (k <: fin (n - 1)) else (k - 1 <: fin (n - 1)))
        in
        let i1, i2 = pigeonhole reduced_s in
        i1 + 1, i2 + 1

(* Tentative generalization of pigeonhole principle *)
(* let rec pigeonhole_gen_aux *)
(*   (#n:int{n > 0}) *)
(*   (#k:nat) *)
(*   (v:seqn k (fin n)) *)
(*   (counts:seqn n nat) *)
(*   (seen:seqn n (list (fin k))) *)
(*   (max_count:fin n) *)
(*   (support:fin (n+1)) *)
(*   (i:fin k) *)
(*   : Pure (list (fin k)) *)
(*     (requires ( *)
(*       sum counts = i /\ *)
(*       S.forall2 (fun c l -> c = L.length l) counts seen /\ *)
(*       S.for_alli (fun i l -> L.for_all (fun x -> S.index v x = i) l) seen /\ *)
(*       max_arg counts = max_count /\ *)
(*       L.length (satisfies (fun v -> v = 0) counts) = support /\ *)
(*       (i-1)/support <= S.index counts max_count *)
(*     )) *)
(*     (ensures (fun r -> L.length r >= k / n /\ *)
(*         k > n ==> (let i = S.index v (S.index r 0) in S.for_all (fun x -> S.index v x = i) r) *)
(*     )) *)
(* = *)
(*   let k0 = S.index v i in *)
(*   let c = S.index counts k0 in *)
(*   if c + 1 >= k / n *)
(*   then i :: S.index seen k0 *)
(*   else *)
(*     let counts = upd count k0 (c+1) in *)
(*     if i +1 < k *)
(*     then *)
(*       let seen = upd seen k0 (i::S.index seen k0) in *)
(*       let max_count= *)
(*         if S.index counts max_count < c+1 *)
(*         then k0 *)
(*         else max_count *)
(*       in *)
(*       let support = if c = 0 then support + 1 else support in *)
(*       pigeonhole_gen_aux #n #k v counts seen max_count support (i+1) *)
(*     else *)
(*       (\* In this case we looked at the k elements of v and we know *\) *)
(*       (\* that for each value x in fin n there is *\) *)
(*       (\* [S.index counts x < k/support] indices in v with value x *\) *)
(*       (\* so [k = i+1 = sum counts < n * k/support <= k] which is absurd *\) *)
(* let pigeonhole_gen (#n #k:nat) (v:seqn k (fin n)) *)
(*   : Pure (if n = 0 then False else vect ((k-1)/n) (fin k)) *)
(*     (requires True) *)
(*     (ensures (fun v' -> exists x. L.forallp (fun i -> S.index v i == x) v')) *)
(* = pigeonhole_gen_aux #n #k #n (seqn n nat) *)