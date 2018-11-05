module LowStar.Promote

open FStar.HyperStack.ST
open FStar.Integers
open FStar.ConstantTime.Integers

open LowStar.Buffer

module ST = FStar.HyperStack.ST
module CT = FStar.ConstantTime.Integers

friend FStar.IFC
friend FStar.ConstantTime.Integers

let declassifiable #sw s b b' = b' == b

private
val index_map: #a:Type -> #b:Type -> f:(a -> b) -> l:list a -> i:nat{i < List.Tot.length l} ->
  Lemma (List.Tot.index (List.Tot.map f l) i == f (List.Tot.index l i))
  [SMTPat (List.Tot.index (List.Tot.map f l) i)]
let rec index_map #a #b f l i =
  if i = 0 then ()
  else
    match l with
    | [] -> ()
    | _ :: l' -> index_map f l' (i - 1)

let rec map #a #b f s =
  Seq.lemma_seq_list_bij s;
  Seq.seq_of_list (List.Tot.map f (Seq.seq_to_list s))

let promote #sw b = 
  let h = ST.get () in
  Seq.lemma_eq_intro (as_seq h b) (map (fun x -> CT.promote #_ #lo x hi) (as_seq h b));  
  b

let demote #sw b' b = 
  let h = ST.get () in
  Seq.lemma_eq_intro (as_seq h b) (map (fun x -> CT.promote #_ #lo x hi) (as_seq h b))
