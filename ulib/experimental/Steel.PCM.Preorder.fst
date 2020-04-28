module Steel.PCM.Preorder
open Steel.PCM
open FStar.Preorder

let induces_preorder #a (p:pcm a) (q:preorder a) =
  forall (x y:a). frame_preserving p x y
         ==> (forall (z:a). compatible p x z ==> q z y)

let preorder_of_pcm #a (p:pcm a) : preorder a =
  fun x y -> forall (q:preorder a). induces_preorder p q ==> q x y

let stability #a (fact:a -> prop) (q:preorder a) (p:pcm a)
  : Lemma
    (requires stable fact q /\
              induces_preorder p q)
    (ensures  stable fact (preorder_of_pcm p))
  = ()

let frame_preserving_is_preorder_respecting #a (p:pcm a) (x y:a)
  : Lemma (requires frame_preserving p x y)
          (ensures (forall z. compatible p x z ==> preorder_of_pcm p z y))
  = ()

type wv a = | Witnessed : a -> wv a | Value : a -> wv a

let least #a (q:preorder a) = x:a{forall (y:a). q x y}

let rec qhistory #a (q:preorder a) (l:list a) =
  match l with
  | []
  | [_] -> True
  | x::y::tl -> x `q` y /\ qhistory q (y::tl)

let hist #a (q:preorder a) = l:list a{qhistory q l}

let rec extends #a (#q:preorder a) (h0 h1:hist q) =
  h0 == h1 \/
  (Cons? h0 /\ extends (Cons?.tl h0) h1)

module L = FStar.List.Tot

let rec extends_length_eq #a (#q:preorder a) (h0 h1:hist q)
  : Lemma (ensures (extends h0 h1 ==> h0 == h1 \/ L.length h0 > L.length h1))
          [SMTPat (extends h0 h1)]
  = match h0 with
    | [] -> ()
    | hd::tl -> extends_length_eq tl h1

let p_composable #a (q:preorder a) : symrel (hist q) =
    fun x y -> extends x y \/ extends y x

let p_op #a (q:preorder a) (x:hist q) (y:hist q{p_composable q x y}) : hist q =
  if L.length x >= L.length y
  then x
  else if L.length x = L.length y
  then (assert (x == y); x)
  else y

let p_op_extends #a (q:preorder a) (x:hist q) (y:hist q{p_composable q x y})
  : Lemma (ensures (p_op q x y `extends` x /\
                    p_op q x y `extends` y /\
                    (p_op q x y == x \/ p_op q x y == y)))
          [SMTPat (p_op q x y)]
  = extends_length_eq x y;
    extends_length_eq y x

let rec p_op_nil #a (q:preorder a) (x:hist q)
  : Lemma (ensures (p_composable q x [] /\ p_op q x [] == x))
          [SMTPat (p_composable q x [])]
  = match x with
    | [] -> ()
    | _::tl -> p_op_nil q tl

let p #a (q:preorder a) : pcm' (hist q) = {
  composable = p_composable q;
  op = p_op q;
  one = []
}

let comm #a (q:preorder a) (x y:hist q)
  : Lemma (requires p_composable q x y)
          (ensures p_composable q y x)
  = ()

let comm_op #a (q:preorder a) (x:hist q) (y:hist q{p_composable q x y})
  : Lemma (p_op q x y == p_op q y x)
  = extends_length_eq x y;
    extends_length_eq y x

let rec extends_trans #a (#q:preorder a) (x y z:hist q)
  : Lemma (x `extends` y /\ y `extends` z ==> x `extends` z)
          [SMTPat (x `extends` y);
           SMTPat (y `extends` z)]
  = match x with
    | [] -> ()
    | _::tl -> extends_trans tl y z

let rec extends_disjunction #a (#q:preorder a) (x y z:hist q)
  : Lemma (z `extends` x /\ z `extends` y ==> x `extends` y \/ y `extends` x)
          [SMTPat (z `extends` x);
           SMTPat (z `extends` y)]
  = match z with
    | [] -> ()
    | _::tl -> extends_disjunction x y tl


let pcm_of_preorder #a (q:preorder a) : pcm (hist q) = {
  p = p q;
  comm = comm_op q;
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}

let frame_preserving_q #a (q:preorder a) (x y:hist q) (z:hist q)
  : Lemma (requires (frame_preserving (pcm_of_preorder q) x y /\ compatible (pcm_of_preorder q) x z))
          (ensures (y `extends` z))
  = ()
