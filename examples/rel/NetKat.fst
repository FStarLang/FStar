module NetKat

(* This is a simplified F* version of the NetKat example found in Section 2 of
   the paper "NetKat: Semantic Foundations for Networks" (POPL'14) *)

module S = FStar.Set
module L = FStar.List.Tot

(* "Syntax", from Figure 2. Deeply embedded in F*. *)
type packet =
  list (field * value)

and field =
  string

and value =
  int

and history =
  h:list packet{ L.length h > 0 }

and predicate =
  | PrTrue: predicate
  | PrFalse: predicate
  | PrFieldEq: f:field -> v:value -> predicate
  | PrOr: p1:predicate -> p2:predicate -> predicate
  | PrAnd: p1:predicate -> p2:predicate -> predicate
  | PrNot: p:predicate -> predicate

and policy =
  | PoFilter: p:predicate -> policy
  | PoMod: f:field -> v:value -> policy
  | PoUnion: p1:policy -> p2:policy -> policy
  | PoSeq: p1:policy -> p2:policy -> policy
  | PoStar: p:policy -> policy
  | PoDup: policy

(* Semantics, from Figure 2. Specifically, denotational semantics using sets. *)
let rec s (p: predicate) (h: history): S.set history =
  match p, h with
  | PrTrue, _ ->
      S.singleton h
  | PrFalse, _ ->
      S.empty
  | PrFieldEq f v, h :: hs ->
      begin match L.assoc f h with
      | Some v' ->
          if v = v' then
            S.singleton (h :: hs)
          else
            S.empty
      | None ->
          S.empty
      end
  | PrNot p, h ->
      S.intersect (S.singleton h) (S.complement (s p h))
  | PrOr p1 p2, h ->
      S.union (s p1 h) (s p2 h)
  | PrAnd _ _, _ ->
      admit ()
