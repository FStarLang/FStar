module Huffman

open FStar.Char
open FStar.List.Tot
open FStar.List.Tot

type symbol = char

// could consider moving weights away from the nodes,
// only need one weight per each trie in the forest

type trie =
  | Leaf : w:pos -> s:symbol -> trie
  | Node : w:pos -> l:trie -> r:trie -> trie

let weight (t:trie) : Tot pos =
  match t with
  | Leaf w _ -> w
  | Node w _ _ -> w

let leq_trie (t1:trie) (t2:trie) : Tot bool =
  weight t1 <= weight t2

(* Copied and adapted some part about sorted int lists,
   this should really be generic in the library *)

let rec sorted (ts:list trie) : Tot bool =
  match ts with
  | [] | [_] -> true
  | t1::t2::ts' -> leq_trie t1 t2 && sorted (t2::ts')

type permutation (l1:list trie) (l2:list trie) =
    length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

val sorted_smaller: x:trie
                ->  y:trie
                ->  l:list trie
                ->  Lemma (requires (sorted (x::l) /\ mem y l))
                          (ensures (leq_trie x y))
                          [SMTPat (sorted (x::l)); SMTPat (mem y l)]
let rec sorted_smaller x y l = match l with
    | [] -> ()
    | z::zs -> if z=y then () else sorted_smaller x y zs

let rec insert_in_sorted (x:trie) (xs:list trie) : Pure (list trie)
    (requires (b2t (sorted xs)))
    (ensures (fun ys -> sorted ys /\ permutation (x::xs) ys)) =
  match xs with
  | [] -> [x]
  | x'::xs' -> if leq_trie x x' then x :: xs
               else (let i_tl = insert_in_sorted x xs' in
                     let (z::_) = i_tl in (* <-- needed for triggering patterns? *)
                     x' :: i_tl)

let rec insertion_sort (ts : list trie) : Pure (list trie)
    (requires (True)) (ensures (fun ts' -> sorted ts' /\ permutation ts ts')) =
  match ts with
  | [] -> []
  | t::ts' -> insert_in_sorted t (insertion_sort ts')

let rec huffman_trie (ts:list trie) : Pure trie
    (requires (sorted ts /\ List.Tot.length ts > 0))
    (ensures (fun t ->
      ((List.Tot.length ts > 1 \/ existsb Node? ts) ==> Node? t)))
    (decreases (List.Tot.length ts)) =
  match ts with
  | t1::t2::ts' ->
      assert(List.Tot.length ts > 1); (* so it needs to prove Node? t *)
      let w = weight t1 + weight t2 in
      let t = huffman_trie ((Node w t1 t2) `insert_in_sorted` ts') in
      (* by the recursive call we know:
         (List.Tot.length (Node w t1 t2 `insert_in_sorted` ts') > 1
          \/ existsb Node? (Node w t1 t2 `insert_in_sorted` ts') ==> Node? t) *)
      (* Since ts' could be empty, I thought that the only way we can
         use this is by proving: existsb Node? (Node w t1 t2
         `insert_in_sorted` ts'), which requires induction. But F* was smarter! *)
      if Nil? ts' then
        assert(existsb Node? (Node w t1 t2 `insert_in_sorted` ts'))
      else
        assert(length (Node w t1 t2 `insert_in_sorted` ts') > 1);
      assert(Node? t);
      t
  | [t1] -> t1 (* this uses `existsb Node? [t] ==> Node? t` fact *)

let huffman (sws:list (symbol*pos)) : Pure trie
    (requires (b2t (List.Tot.length sws > 0)))
    (ensures (fun t -> List.Tot.length sws > 1 ==> Node? t)) =
  huffman_trie (insertion_sort (List.Tot.map (fun (s,w) -> Leaf w s) sws))

let rec encode_one (t:trie) (s:symbol) : Tot (option (list bool)) =
  match t with
  | Leaf _ s' -> if s = s' then Some [] else None
  | Node _ t1 t2 ->
      match encode_one t1 s with
      | Some bs -> Some (false :: bs)
      | None -> match encode_one t2 s with
                | Some bs -> Some (true :: bs)
                | None -> None

// Modulo the option this is flatten (map (encode_one t) ss)
let rec encode (t:trie) (ss:list symbol) : Pure (option (list bool))
    (requires (True))
    (ensures (fun bs -> Node? t /\ Cons? ss /\ Some? bs
                        ==> Cons? (Some?.v bs))) =
  match ss with
  | [] -> None (* can't encode the empty string *)
  | [s] -> encode_one t s
  | s::ss' -> match encode_one t s, encode t ss' with
              | Some bs, Some bs' -> Some (bs @ bs')
              | _, _ -> None

// A more complex decode I originally wrote

let rec decode_one (t:trie) (bs:list bool) : Pure (option (symbol * list bool))
    (requires (True))
    (ensures (fun r -> Some? r ==>
                   (List.Tot.length (snd (Some?.v r)) <= List.Tot.length bs /\
     (Node? t ==> List.Tot.length (snd (Some?.v r)) < List.Tot.length bs)))) =
  match t, bs with
  | Node _ t1 t2, b::bs' -> decode_one (if b then t2 else t1) bs'
  | Leaf _ s, _ -> Some (s, bs)
  | Node _ _ _, [] -> None (* out of symbols *)

let rec decode' (t:trie) (bs:list bool) : Tot (option (list symbol))
    (decreases (List.Tot.length bs)) =
  match t, bs with
  | Leaf _ s, [] -> Some [s] (* degenerate case, case omitted below *)
  | Leaf _ _, _::_  -> None (* too many symbols, case omitted below *)
  | Node _ _ _, [] -> Some []
  | Node _ _ _, _::_ -> match decode_one t bs with
                        | Some (s, bs') -> (match decode' t bs' with
                                            | Some ss -> Some (s :: ss)
                                            | None    -> None)
                        | _ -> None

// Simplified decode using idea from Bird and Wadler's book
// (it has more complex termination condition though)

let rec decode_aux (t':trie{Node? t'}) (t:trie) (bs:list bool) :
  Pure (option (list symbol))
    (requires (True))
    (ensures (fun ss -> Some? ss ==> List.Tot.length (Some?.v ss) > 0))
    (decreases (%[bs; if Leaf? t && Cons? bs then 1 else 0]))
  =
  match t, bs with
  | Leaf _ s, [] -> Some [s]
  | Leaf _ s, _::_ -> (match decode_aux t' t' bs with
                      | Some ss -> Some (s :: ss)
                      | None -> None)
  | Node _ t1 t2, b :: bs' -> decode_aux t' (if b then t2 else t1) bs'
  | Node _ _ _, [] -> None

let decode (t:trie) (bs:list bool) : Pure (option (list symbol))
    (requires (b2t (Node? t))) (ensures (fun _ -> True)) =
  decode_aux t t bs

let rec cancelation_one (t':trie) (t:trie) (s:symbol) : Lemma
  (requires (b2t (Node? t')))
  (ensures (Node? t' ==>
            (match encode_one t s with
            | Some e -> (match decode_aux t' t e with
                        | Some d -> d = [s]
                        | None -> False)
            | None -> True))) (decreases t) =
  match t with
  | Leaf _ s' -> ()
  | Node _ t1 t2 ->
      (match encode_one t1 s with
      | Some e -> cancelation_one t' t1 s
      | None   -> cancelation_one t' t2 s)

let rec decode_prefix_aux (t':trie{Node? t'}) (t:trie)
    (bs:list bool) (bs':list bool) (s:symbol) : Lemma
    (requires (decode_aux t' t bs = Some [s]))
    (ensures (Cons? bs' ==> decode_aux t' t (bs @ bs') =
                                     (match decode_aux t' t' bs' with
                                     | Some ss -> Some (s :: ss)
                                     | None -> None)))
    (decreases (%[bs; if Leaf? t && Cons? bs then 1 else 0])) =
  match t, bs with
  | Leaf _ _, [] -> ()
  | Leaf _ _, _::_ -> decode_prefix_aux t' t' bs bs' s
  | Node _ t1 t2, b::bs'' ->
      decode_prefix_aux t' (if b then t2 else t1) bs'' bs' s

let rec decode_prefix (t:trie{Node? t})
  (bs:list bool) (bs':list bool{Cons? bs'}) (s:symbol) : Lemma
  (requires (decode t bs = Some [s]))
  (ensures (decode t (bs @ bs') = (match decode t bs' with
                                   | Some ss -> Some (s :: ss)
                                   | None -> None))) =
  decode_prefix_aux t t bs bs' s

let rec cancelation_aux (t:trie{Node? t}) (ss:list symbol) : Lemma
  (requires (True))
  (ensures (match encode t ss with
            | Some e -> (match decode t e with
                        | Some d -> d = ss
                        | None -> False)
            | None -> True)) (decreases ss) =
  match ss with
  | [] -> ()
  | [s] -> cancelation_one t t s
  | s::ss' ->
    cancelation_one t t s;
    cancelation_aux t ss';
    (match encode_one t s, encode t ss' with
    | Some bs, Some bs' -> decode_prefix t bs bs' s
    | _, _ -> ())

let rec cancelation (sws:list (symbol*pos)) (ss:list symbol) : Lemma
  (requires (b2t (List.Tot.length sws > 1)))
  (ensures (List.Tot.length sws > 1 ==>
            (let t = huffman sws in
            (match encode t ss with
            | Some e -> (match decode t e with
                        | Some d -> d = ss
                        | None -> False)
            | None -> True)))) =
  cancelation_aux (huffman sws) ss

(* Some References:

David A. Huffman. A Method for the Construction of Minimum-Redundancy Codes.
Proc. IRE, pp. 1098-1101, September 1952.
http://compression.ru/download/articles/huff/huffman_1952_minimum-redundancy-codes.pdf

Bird, R., Wadler, P.: Introduction to Functional Programming. Prentice
Hall International Series in Computer Science. Prentice Hall, Hemel
Hempstead, UK (1988). Pages 239--246.
https://usi-pl.github.io/lc/sp-2015/doc/Bird_Wadler.%20Introduction%20to%20Functional%20Programming.1ed.pdf

Jasmin Christian Blanchette.
Proof Pearl: Mechanizing the Textbook Proof of Huffman’s Algorithm.
Journal of Automated Reasoning. June 2009, Volume 43, Issue 1, pp 1–18.
http://people.mpi-inf.mpg.de/~jblanche/jar2009-huffman.pdf
- only proves optimality, doesn't even implement encode/decode

Laurent Théry. Formalising Huffman algorithm.
https://github.com/coq-contribs/huffman
ftp://ftp-sop.inria.fr/marelle/Laurent.Thery/Huffman/Note.pdf
- does include encode/decode

*)
