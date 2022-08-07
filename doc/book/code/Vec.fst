module Vec

//SNIPPET_START: even_and_odd
type even (a:Type) =
 | ENil : even a
 | ECons : a -> odd a -> even a
and odd (a:Type) =
 | OCons : a -> even a -> odd a
//SNIPPET_END: even_and_odd

//SNIPPET_START: elength_and_olength
let rec elength #a (e:even a)
  : n:nat { n % 2 == 0}
  = match e with
    | ENil -> 0
    | ECons _ tl -> 1 + olength tl
and olength #a (o:odd a)
  : n:nat { n % 2 == 1 }
  = let OCons _ tl = o in
    1 + elength tl
//SNIPPET_END: elength_and_olength

//SNIPPET_START: even_or_odd_list
type even_or_odd_list (a:Type) : bool -> Type =
 | EONil : even_or_odd_list a true
 | EOCons : a -> #b:bool -> even_or_odd_list a b -> even_or_odd_list a (not b)
//SNIPPET_END: even_or_odd_list

//SNIPPET_START: eo_length
let rec eo_length #a #b (l:even_or_odd_list a b)
  : Tot (n:nat { if b then n % 2 == 0 else n % 2 == 1})
        (decreases l)
  = match l with
    | EONil -> 0
    | EOCons _ tl -> 1 + eo_length tl
//SNIPPET_END: eo_length


//SNIPPET_START: vec
type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
//SNIPPET_END: vec

[@@unifier_hint_injective]
let vec' (a:Type) (n:nat) = vec a n

//SNIPPET_START: long_get
let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = match v with
    | Nil -> false_elim()
    | Cons hd tl ->
      if i = 0 then hd
      else get (i - 1) tl
//SNIPPET_END: long_get

[@@expect_failure] //duplicate_name
//SNIPPET_START: get
let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = let Cons hd tl = v in
    if i = 0 then hd
    else get (i - 1) tl
//SNIPPET_END: get

//SNIPPET_START: split_at
let rec split_at #a #n (i:nat{i <= n}) (v:vec a n)
  : vec a i & vec a (n - i)
  = if i = 0
    then Nil, v
    else let Cons hd tl = v in
         let l, r = split_at (i - 1) tl in
         Cons hd l, r
//SNIPPET_END: split_at

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


//SNIPPET_START: split_at_tail
let split_at_tail #a #n (i:nat{i <= n}) (v:vec a n)
  : vec a i & vec a (n - i)
  = let rec aux (j:nat{j <= i})
                (v:vec a (n - (i - j)))
                (out:vec a (i - j))
      : vec a i & vec a (n - i)
      = if j = 0
        then reverse out, v
        else let Cons hd tl = v in
             aux (j - 1) tl (Cons hd out)
    in
    aux i v Nil
//SNIPPET_END: split_at_tail

//SNIPPET_START: foldr
let rec foldr #a #n #acc
              (f:a -> acc -> acc)
              (v:vec a n)
              (init:acc)
  : acc
  = match v with
    | Nil -> init
    | Cons hd tl ->
      f hd (foldr f tl init)
//SNIPPET_END: foldr

//SNIPPET_START: norm_spec
open FStar.Mul

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

open FStar.Tactics
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
