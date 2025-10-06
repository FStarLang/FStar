module Param

open FStar.Tactics.V2
open FStar.Tactics.Parametricity

(***** Unary nats *)

type nat =
  | Z
  | S of nat

%splice[nat_param; Z_param; S_param] (paramd (`%nat))

let safepred (x:nat) : nat =
  match x with
  | Z -> Z
  | S x -> x

%splice[safepred_param] (paramd (`%safepred))

(***** Pairs *)

// Universe polymorphism currently broken in tactics
let fst (#a #b : Type0) (p : a & b) : a =
  match p with
  | Mktuple2 x y -> x <: a

let snd (#a #b : Type0) (p : a & b) : b =
  match p with
  | Mktuple2 x y -> y <: b

%splice[tuple2_param] (paramd (`%tuple2))

%splice[fst_param] (paramd (`%fst))

%splice[snd_param] (paramd (`%snd))

(***** Lists *)

%splice[list_param; Nil_param; Cons_param] (paramd (`%list))

//[@@erasable]
//noeq
//type list_param (a1:Type u#aa) (a2:Type u#aa) (ar:a1 -> a2 -> Type0) : list a1 -> list a2 -> Type u#aa =
//  | Nil_param : list_param a1 a2 ar [] []
//  | Cons_param : (h1:a1) -> (h2:a2) -> (hr:ar h1 h2) ->
//                 (t1:list a1) -> (t2:list a2) -> (tr:list_param a1 a2 ar t1 t2) ->
//                 list_param a1 a2 ar (h1::t1) (h2::t2)

let safetail (#a:Type0) (x:list a) : list a =
  match x with
  | [] -> []
  | x::xs -> xs

let safetail_param_manual
  (#a #b : Type0) (#r : a -> b -> Type0)
  (l0:list a) (l1:list b) (lR : list_param a b r l0 l1)
: list_param a b r (safetail l0) (safetail l1)
// ^ needed!!!
=
  match lR with
  | Nil_param -> Nil_param
  | Cons_param _ _ _ _ _ r -> r

%splice[safetail_param] (paramd (`%safetail))


(***** Misc *)

let test0 : int = 2

%splice[test0_param] (paramd (`%test0))

let int_int_t = int -> int
%splice[int_int_t_param] (paramd (`%int_int_t))

let my_int : Type = Prims.int
%splice[my_int_param] (paramd (`%my_int))

let test1 : Type u#2 = Type u#1

[@@expect_failure] // FIXME
%splice[test1_param] (paramd (`%test1))

let test2 = bd1:Type -> bd2:Type -> bd1

[@@expect_failure] // FIXME
%splice[test2_param] (paramd (`%test2))

let id_t = #a:Type -> a -> a

[@@expect_failure] // FIXME
%splice[id_t_param] (paramd (`%id_t))

let id (#a:Type0) (x:a) : a = x
%splice[id_param] (paramd (`%id))

//let id_is_unique (f : (#a:Type -> a -> a)) (f_parametric : id_t_param f f) : Lemma (forall a (x:a). f x == x) =
//  let aux (a:Type) (x:a) : Lemma (f x == x) =
//    f_parametric (fun y () -> squash (x == y)) x () ()
//  in
//  Classical.forall_intro_2 aux

//let test () = id_is_unique id id_param

let binop_t = #a:Type -> a -> a -> a
//%splice[binop_t_param] (paramd (`%binop_t))

//let binop_is_fst_or_snd_pointwise (f : (#a:Type -> a -> a -> a)) (f_param : binop_t_param f f)
//  : Lemma (forall a (x y : a). f x y == x \/ f x y == y)
//  =
//  let aux a (x y : a) : Lemma (f x y == x \/ f x y == y) =
//   f_param (fun z () -> squash (z == x \/ z == y)) x () () y () ()
//  in
//  Classical.forall_intro_3 aux
//
//let binop_is_fst_or_snd_extensional (f : (#a:Type -> a -> a -> a)) (f_param : binop_t_param f f)
//  : Lemma ((forall a (x y : a). f x y == x) \/ (forall a (x y : a). f x y == y))
//  =
//  binop_is_fst_or_snd_pointwise f f_param;
//  assert (f 1 2 == 1 \/ f 1 2 == 2);
//  let aux1 (_ : squash (f 1 2 == 1))
//           a (x y : a) : Lemma (f x y == x) =
//   f_param (fun z i -> squash (i == 1 ==> z == x)) x 1 () y 2 ()
//  in
//  let aux2 (_ : squash (f 1 2 == 2))
//           a (x y : a) : Lemma (f x y == y) =
//   f_param (fun z i -> squash (i == 2 ==> z == y)) x 1 () y 2 ()
//  in
//  let aux1' () : Lemma (requires (f 1 2 == 1)) (ensures (forall a (x y : a). f x y == x)) =
//    Classical.forall_intro_3 (aux1 ())
//  in
//  let aux2' () : Lemma (requires (f 1 2 == 2)) (ensures (forall a (x y : a). f x y == y)) =
//    Classical.forall_intro_3 (aux2 ())
//  in
//  Classical.move_requires aux1' ();
//  Classical.move_requires aux2' ()

let test_int_to_int = int -> int
%splice [test_int_to_int_param] (paramd (`%test_int_to_int))

[@@(preprocess_with param)]
let test_list_0 = list

[@@(preprocess_with param)]
let test_list = list int

[@@(preprocess_with param)]
let rev_param = #a:Type -> list a -> list a

// GM: squash needed
let rel_of_fun #a #b (f : a -> b) : a -> b -> Type =
  fun x y -> squash (y == f x)

let rec list_rec_of_function_is_map_1 #a #b (f : a -> b) (l1 : list a) (l2 : list b)
                                            (p : list_param _ _ (rel_of_fun f) l1 l2)
        : Lemma (l2 == List.Tot.map f l1)
 = match p with
   | Nil_param -> ()
   | Cons_param _ _ _ _ _ t -> list_rec_of_function_is_map_1 _ _ _ t

let rec list_rec_of_function_is_map_2 #a #b (f : a -> b) (l1 : list a) (l2 : list b)
        : Pure (list_param _ _ (rel_of_fun f) l1 l2)
               (requires (l2 == List.Tot.map f l1))
               (ensures (fun _ -> True))
 = match l1, l2 with
   | Nil, Nil -> Nil_param
   | Cons h1 t1, Cons h2 t2 ->
     Cons_param h1 h2 () _ _ (list_rec_of_function_is_map_2 f t1 t2)

let reverse_commutes_with_map
    (rev : (#a:Type u#a -> list a -> list a)) // doesn't really have to be "reverse"...
    (rev_is_param : rev_param rev rev)
    : Lemma (forall (a:Type u#a) (b:Type u#a) (f : a -> b) l. rev (List.Tot.map f l) == List.Tot.map f (rev l))
    =
  let aux a b f l : Lemma (rev (List.Tot.map f l) == List.Tot.map f (rev l)) =
    let rel_f : a -> b -> Type = rel_of_fun f in
    let rpf = list_rec_of_function_is_map_2 f l (List.Tot.map f l) in
    let rpf2 = rev_is_param #_ #_ #rel_f l (List.Tot.map f l) rpf in
    list_rec_of_function_is_map_1 f (rev l) (rev (List.Tot.map f l)) rpf2;
    ()
  in
  Classical.forall_intro_4 aux

let rec app (#a:Type) (l1 l2 : list a) : list a =
  match l1 with
  | [] -> l2
  | h::t -> h :: (app t l2)

let rec app_rel (#a0:Type) (#a1:Type) (aR : a0 -> a1 -> Type)
            (l11 : list a0) (l12 : list a1) (l1R : list_param _ _ aR l11 l12)
            (l21 : list a0) (l22 : list a1) (l2R : list_param _ _ aR l21 l22)
            : list_param a0 a1 aR (l11 `app` l21) (l12 `app` l22) =
   match l11, l12 with
   | [], [] -> l2R
   | h1::t1, h2::t2 ->
     begin match l1R with
     | Cons_param _ _ hr _ _ tr -> Cons_param h1 h2 hr (app t1 l21) (app t2 l22) (app_rel aR t1 t2 tr l21 l22 l2R)
     end


let rec reverse (#a:Type) (l : list a) : list a =
  match l with
  | [] -> []
  | x::xs -> reverse xs `app` [x]

let rec reverse_rel (#a0:Type) (#a1:Type) (#aR: a0 -> a1 -> Type)
                    (l0 : list a0) (l1 : list a1) (lR : list_param _ _ aR l0 l1)
                  : list_param _ _ aR (reverse l0) (reverse l1) =
  match l0, l1 with
  | [], [] -> Nil_param
  | h1::t1, h2::t2 ->
    begin match lR with
    | Cons_param _ _ hr _ _ tr ->
    app_rel aR (reverse t1) (reverse t2) (reverse_rel t1 t2 tr)
               [h1] [h2] (Cons_param h1 h2 hr Nil Nil Nil_param)
    end

(* Doesn't work by SMT, and tactic above does not handle fixpoints.
 * What to do about them? Is there a translation for general recursion?
 * Should read https://openaccess.city.ac.uk/id/eprint/1072/1/PFF.pdf in
 * more detail. *)
(* ^ stale comment, using inductive proofs right now *)

let real_reverse_commutes_with_map ()
  : Lemma (forall (a b:Type u#a) (f : a -> b) l. reverse (List.Tot.map f l) == List.Tot.map f (reverse l))
  = reverse_commutes_with_map u#a reverse reverse_rel

(* 2020/07/23: This doesn't work from outside this module... why? *)

type label =
  | Low
  | High

%splice[label_param] (paramd (`%label))

noeq type labeled_interface : Type u#(1 + a) = {
  labeled : Type u#a -> Type u#a;
  mk_labeled : #a:Type u#a -> a -> label -> labeled a;
  label_of : #a:Type u#a -> labeled a -> label;
}

%splice[labeled_interface_param] (paramd (`%labeled_interface))

// From here onwards, every u#0 should be an u#a

let proj_labeled (r:labeled_interface u#0) : Type u#0 -> Type u#0 =
  match r with
  | Mklabeled_interface l m lo -> l

let proj_mk_labeled (r:labeled_interface u#0) : #a:Type u#0 -> a -> label -> (proj_labeled r) a =
  match r with
  | Mklabeled_interface l m lo -> m

let proj_label_of (r:labeled_interface u#0) : #a:Type u#0 -> (proj_labeled r) a -> label =
  match r with
  | Mklabeled_interface l m lo -> lo

%splice[proj_labeled_param] (paramd (`%proj_labeled))

%splice[proj_mk_labeled_param] (paramd (`%proj_mk_labeled))

%splice[proj_label_of_param] (paramd (`%proj_label_of))

let lab_impl : labeled_interface = {
  labeled = (fun (a:Type) -> a & label);
  mk_labeled = (fun (#a:Type) (x:a) (l:label) -> (x,l));
  label_of = (fun (#a:Type) x -> snd x);
}

%splice[lab_impl_param] (paramd (`%lab_impl))
