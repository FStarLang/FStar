module Bug4601

(* An extra hypothesis restating a refinement made Z3 4.13.3 answer
   "unknown (incomplete quantifiers)" for bad. Verifies with Z3 5.3.0. *)
module S = FStar.Set

let rec sorted (#a:eqtype) (f:a -> a -> bool) (l:list a) : Tot bool =
  match l with
  | [] -> true
  | x::[] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

type ordset (a:eqtype) (f:a -> a -> bool) = l:list a{sorted f l}

assume val intersect (#a:eqtype) (#f:a -> a -> bool) (s1 s2: ordset a f)
  : z:ordset a f{forall x. List.Tot.mem x z = (List.Tot.mem x s1 && List.Tot.mem x s2)}

let rec as_set (#a:eqtype) (#f:a -> a -> bool) (s:ordset a f) : Tot (S.set a) =
  match s with
  | [] -> S.empty
  | hd::tl -> S.union (S.singleton hd) (as_set #a #f tl)

let rec lemma_as_set_mem (#a:eqtype) (#f:a -> a -> bool) (s:ordset a f) (x:a)
  : Lemma (List.Tot.mem x s <==> S.mem x (as_set s))
          [SMTPat (List.Tot.mem x s); SMTPat (S.mem x (as_set s))]
  = match s with
    | [] -> ()
    | hd::tl -> if x = hd then () else lemma_as_set_mem #a #f tl x

let good (#a:eqtype) (#f:a -> a -> bool) (s1 s2: ordset a f)
  : Lemma (requires S.disjoint (as_set s1) (as_set s2))
          (ensures intersect s1 s2 = []) =
  let mem_eq p (q:ordset a f) : Lemma (S.mem p (as_set q) <==> List.Tot.mem p q) = () in
  Classical.forall_intro_2 mem_eq

let bad (#a:eqtype) (#f:a -> a -> bool) (s1 s2: ordset a f)
  : Lemma (requires S.disjoint (as_set s1) (as_set s2) /\ sorted f (intersect s1 s2))
          (ensures intersect s1 s2 = []) =
  let mem_eq p (q:ordset a f) : Lemma (S.mem p (as_set q) <==> List.Tot.mem p q) = () in
  Classical.forall_intro_2 mem_eq
