module Huffman

open FStar.Char
open FStar.List.Tot

type symbol = char

// TODO: could move weights away from the nodes,
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

let rec sorted (ts:list trie) : Tot bool=
  match ts with
  | [] | [_] -> true
  | t1::t2::ts' -> leq_trie t1 t1 && sorted (t2::ts')

let rec insert_in_sorted (x:trie) (xs:list trie) : Pure (list trie)
    (requires (b2t (sorted xs)))
    (ensures (fun ys -> sorted ys
           /\ List.Tot.length ys == List.Tot.length xs + 1)) =
  match xs with
  | [] -> [x]
  | x'::xs' -> if leq_trie x x' then x :: xs
               else x' :: (insert_in_sorted x xs')

let rec insertion_sort (ts : list trie) : Pure (list trie)
    (requires (True)) (ensures (fun ts -> sorted ts)) =
  match ts with
  | [] -> []
  | t::ts' -> insert_in_sorted t (insertion_sort ts')

let rec lemma_that_needs_induction (w:pos) (t1:trie) (t2:trie) (ts:list trie) :
  Lemma
    (requires (b2t (sorted ts)))
    (ensures (sorted ts ==> (* without sorted the error message is amazing! *)
              existsb #trie is_Node ((Node w t1 t2) `insert_in_sorted` ts)))
    (decreases ts) =
  match ts with
    | [] -> ()
    | t::ts' -> if leq_trie (Node w t1 t2) t then ()
                else lemma_that_needs_induction w t1 t2 ts'

(* TODO: This magically derives lemma_that_needs_induction? WTF? *)
let rec huffman_trie (ts:list trie) : Pure trie
    (requires (sorted ts /\ List.Tot.length ts > 0))
    (ensures (fun t ->
      (List.Tot.length ts > 1 \/ existsb is_Node ts ==> is_Node t)))
    (decreases (List.Tot.length ts)) =
  match ts with
  | t1::t2::ts' ->
      assert(List.Tot.length ts > 1); (* so it needs to prove is_Node for t *)
      let w = weight t1 + weight t2 in
      let t = huffman_trie (Node w t1 t2 `insert_in_sorted` ts') in
      (* by the recursive call we know:
         (List.Tot.length (Node w t1 t2 `insert_in_sorted` ts') > 1
          \/ existsb is_Node (Node w t1 t2 `insert_in_sorted` ts') ==> is_Node t) *)
      (* I think tht the only way we can use this is by proving:
          existsb is_Node (Node w t1 t2 `insert_in_sorted` ts') *)
      (* but somehow F* manages to prove this without! the following assert fails
         without lemma_that_needs_induction (but works with it)
         lemma_that_needs_induction w t1 t2 ts';
         assert(existsb is_Node (Node w t1 t2 `insert_in_sorted` ts')); *)
      t
  | [t1] -> t1

let huffman (sws:list (symbol*pos)) : Pure trie
    (requires (b2t (List.Tot.length sws > 0)))
    (ensures (fun t -> List.Tot.length sws > 1 ==> is_Node t)) =
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
let rec encode (t:trie) (ss:list symbol) : Tot (option (list bool)) =
  match ss with
  | [] -> Some []
  | s::ss' -> match encode_one t s, encode t ss' with
              | Some bs, Some bs' -> Some (bs @ bs')
              | _, _ -> None

// A more complex decode I originally wrote

let rec decode_one (t:trie) (bs:list bool) : Pure (option (symbol * list bool))
    (requires (True))
    (ensures (fun r -> is_Some r ==>
                   (List.Tot.length (snd (Some.v r)) <= List.Tot.length bs /\
     (is_Node t ==> List.Tot.length (snd (Some.v r)) < List.Tot.length bs)))) =
  match t, bs with
  | Node _ t1 t2, b::bs' -> decode_one (if b then t2 else t1) bs'
  | Leaf _ s, _ -> Some (s, bs)
  | Node _ _ _, [] -> None (* out of symbols *)

let rec decode (t:trie) (bs:list bool) : Tot (option (list symbol))
    (decreases (List.Tot.length bs)) =
  match t, bs with
  | Leaf _ s, [] -> Some [s] (* degenerate case *)
  | Leaf _ _, _  -> None (* too many symbols *)
  | Node _ _ _, [] -> Some []
  | Node _ _ _, _::_ -> match decode_one t bs with
                        | Some (s, bs') -> (match decode t bs' with
                                            | Some ss -> Some (s :: ss)
                                            | None    -> None)
                        | _ -> None

// Simplified decode using idea from Bird and Wadler's book

let rec decode_aux (t':trie) (t:trie) (bs:list bool) : Pure (option (list symbol))
    (requires (b2t (is_Node t'))) (ensures (fun _ -> True))
    (decreases (%[bs; if is_Leaf t && is_Cons bs then 1 else 0]))
  =
  match t, bs with
  | Leaf _ s, [] -> Some [s]
  | Leaf _ s, _::_ -> (match decode_aux t' t' bs with
                      | Some ss -> Some (s :: ss)
                      | None -> None)
  | Node _ t1 t2, b :: bs' -> decode_aux t' (if b then t2 else t1) bs'
  | Node _ _ _, [] -> None

let decode' (t:trie) (bs:list bool) : Pure (option (list symbol))
    (requires (b2t (is_Node t))) (ensures (fun _ -> True)) =
  decode_aux t t bs

// proving this should require prefix freedom
let cancelation (sws:list (symbol*pos)) (ss:list symbol) : Lemma
  (requires (b2t (List.Tot.length sws > 0)))
  (ensures (List.Tot.length sws > 1 ==>
            (let t = huffman sws in
            (match encode t ss with
            | Some e -> (match decode' t e with
                        | Some d -> d = ss
                        | None -> True)
            | None -> True)))) = admit()










(* open Platform.Bytes *)

(* val huffman_trie : ss:(list (symbol * pos)) -> Pure trie *)
(*   (requires (b2t (sorted ss))) *)
(*   (ensures (fun cs -> True)) *)

(* assume val trie_to_code : trie -> Tot (list byte) // symbols as well? *)

(* assume val huffman_code : ss:(list (symbol * pos)) -> Pure (list bytes) *)
(*   (requires (b2t (sorted ss))) *)
(*   (ensures (fun cs -> List.Tot.length cs == List.Tot.length ss)) *)

(* val code_length : ss:(list (symbol * pos)) -> cs:(list bytes) -> Pure nat *)
(*   (requires (sorted ss /\ List.Tot.length cs == List.Tot.length ss)) *)
(*   (ensures (fun _ -> True)) *)
(* let code_length ss cs = *)
(*   fold_left2 (fun (a:nat) (sw:symbol*pos) c -> *)
(*               let (s,w) = sw in *)
(*               a + w `op_Multiply` length c) 0 ss cs *)

(* assume val minimality : ss:(list (symbol * pos)) -> cs:list bytes -> Lemma *)
(*   (requires (sorted ss)) -- need more conditions on cs, needs to be an encoding *)
(*   (ensures (code_length ss (huffman_code ss) >= code_length ss cs)) *)




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
- proves optimality, doesn't even implement encode/decode

Laurent Théry. Formalising Huffman algorithm. 
https://github.com/coq-contribs/huffman
ftp://ftp-sop.inria.fr/marelle/Laurent.Thery/Huffman/Note.pdf
- does include encode/decode

*)
