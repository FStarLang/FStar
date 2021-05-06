module Vec

//SNIPPET_START: vec
type vec a : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
//SNIPPET_END: vec

//SNIPPET_START: append
let rec append #a #n #m (v1:vec a n) (v2:vec a m)
  : vec a (n + m)
  = match v1 with
    | Nil -> v2
    | Cons hd tl -> Cons hd (append tl v2)
//SNIPPET_END: append

//SNIPPET_START: reverse
let rec reverse #a #n (v:vec a n)
  : vec a n
  = match v with
    | Nil -> Nil
    | Cons hd tl -> append (reverse tl) (Cons hd Nil)
//SNIPPET_END: reverse

//SNIPPET_START: get
let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = let Cons hd tl = v in
    if i = 0 then hd
    else get (i - 1) tl
//SNIPPET_END: get

open FStar.Mul

//SNIPPET_START: norm_spec
let rec pow2 (n:nat) : nat =
  if n = 0 then 1
  else 2 * pow2 (n - 1)

let proof_by_normalization ()
  : Lemma (pow2 12 == 4096)
  = normalize_term_spec (pow2 12)
//SNIPPET_END: norm_spec

let rec fold_right (f:'b -> 'a -> 'a) (l:list 'b) (x:'a) =
  match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

module T = FStar.Tactics

//SNIPPET_START: trefl
let partially_reduce_fold_right f more
  : (fold_right f ([1;2;3]@more) 0 == f 1 (f 2 (f 3 (fold_right f more 0))))
  =  _ by (T.trefl())
//SNIPPET_END: trefl

private val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            Lemma (a ==> b)
let imp_intro_lem #a #b f =
  FStar.Classical.give_witness (FStar.Classical.arrow_to_impl (fun (x:squash a) -> FStar.Squash.bind_squash x f))

let lem #a #b (f:a -> b) : (a ==> b) =
  imp_intro_lem (fun x -> FStar.Squash.return_squash (f x));
  assert (a ==> b);
  let x : squash (a ==> b) = () in
  FStar.Squash.join_squash x

let implies_intro () : Tac binder =
  apply (`lem);
  intro()


private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

let split_lem' (#a:Type) (#b:Type) (x:a) (y:b) : (a /\ b) =
  assert (a /\ b);
  let x : squash (a /\ b) = () in
  FStar.Squash.join_squash x

let split () : Tac unit =
  apply (`split_lem')

//SNIPPET_START: tac
let a_very_explicit_tactic_proof (a b : prop) : (a ==> b ==> b /\ a)
  = _ by
       (let ha = implies_intro () in
        let hb = implies_intro () in
        split ();
        hyp hb;
        hyp ha;
        qed ())
//SNIPPET_END: tac
