module Bug1043

open FStar.List

let rec memP_append #a (x: a) (l: list a) :
  Lemma (List.memP x l ==>
         (exists (l1 l2: list a). l == l1 @ (x :: l2))) =
    match l with
    | [] -> ()
    | h :: t ->
      FStar.Classical.or_elim
        #(x == h)
        #(memP x t)
        #(fun _ -> exists (l1 l2: list a). l == l1 @ (x :: l2))
        (fun _ -> assert (l == [] @ (x :: t)))
        (fun _ -> let (l1, l2) = memP_append x t in ())
