(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.OrdSet

type ordset a f = l:(list a){sorted f l}

let hasEq_ordset _ _ = ()

let as_list #_ #_ s = s

let empty #_ #_ = []

let mem #_ #_ x s = List.Tot.mem x s

private val insert': #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){let s = as_list s in let l = as_list l in
	                           (Cons? l /\
                                    (Cons?.hd l = x \/
                                    (Cons? s /\ Cons?.hd l = Cons?.hd s)))})
let rec insert' #_ #f x s =
  match s with
  | []     -> [x]
  | hd::tl ->
    if x = hd then hd::tl
    else if f x hd then x::hd::tl
    else hd::(insert' #_ #f x tl)

let rec union #_ #_ s1 s2 = match s1 with
  | []     -> s2
  | hd::tl -> union tl (insert' hd s2)

let rec intersect #a #f s1 s2 = match s1 with
  | []     -> []
  | hd::tl ->
    if mem #_ #f hd s2 then
      insert' #_ #f hd (intersect #_ #f tl s2)
    else
      intersect #_ #f tl s2

let choose #a #f s = match s with
  | []   -> None
  | x::_ -> Some x

private val remove': #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){let s = as_list s in let l = as_list l in
	                           ((Nil? s ==> Nil? l) /\
                                    (Cons? s ==> Cons?.hd s = x ==> l = Cons?.tl s) /\
                                    (Cons? s ==> Cons?.hd s =!= x ==> (Cons? l /\ Cons?.hd l = Cons?.hd s)))})
let rec remove' #a #f x s = match s with
  | []     -> []
  | hd::tl ->
    if x = hd then tl
    else hd::(remove' #_ #f x tl)

let remove #a #f x s = remove' #_ #f x s

let size #a #f s = List.Tot.length s

let rec subset #a #f s1 s2 = match s1, s2 with
  | [], _          -> true
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset #a #f tl tl'
    else if f hd hd' && not (hd = hd') then false
    else subset #a #f s1 tl'
  | _, _           -> false

let singleton (#a:eqtype) #f x = [x]

private
let rec remove_le #a #f x (s:ordset a f)
  : Pure (ordset a f)
    (requires True)
    (ensures (fun r -> let r = as_list r in sorted f (x :: r)))
    (decreases s)
=
  match s with
  | [] -> []
  | y :: ys ->
    if f x y && x <> y
    then s
    else remove_le #a #f x ys

private
let rec minus' (#a:eqtype) (#f:cmp a) (x:a) (s1 s2:ordset a f)
  : Pure (ordset a f)
    (requires (let s1 = as_list s1 in let s2 = as_list s2 in sorted f (x::s1) /\ sorted f (x::s2)))
    (ensures (fun r -> let r = as_list r in sorted f (x::r)))
    (decreases s1)
=
  match s1 with
  | [] -> []
  | x1 :: xs1 ->
    assert (sorted f xs1) ;
    match s2 with
    | [] -> s1
    | x2 :: xs2 ->
      assert (sorted f xs1) ;
      if x1 = x2
      then minus' #a #f x xs1 xs2
      else x1 :: (minus' #a #f x1 xs1 (remove_le x1 s2))

let minus #a #f s1 s2 =
  match s1 with
  | [] -> []
  | x1 :: xs1 -> minus' #a #f x1 xs1 (remove_le #a #f x1 s2)

let strict_subset #a #f s1 s2 = s1 <> s2 && subset #a #f s1 s2

private val set_props:
  #a:eqtype -> #f:cmp a -> s:ordset a f{Cons? (as_list s)}
  -> Lemma (requires True)
          (ensures  (let s = as_list s in
	             (forall x. List.Tot.mem x (Cons?.tl s) ==> (f (Cons?.hd s) x /\ Cons?.hd s =!= x))))
let rec set_props (#a:eqtype) #f s = match s with
  | x::tl -> if tl = [] then () else set_props #a #f tl

private val hd_unique: #a:eqtype -> #f:cmp a -> s:ordset a f
               -> Lemma (requires (Cons? (as_list s)))
                       (ensures (let s = as_list s in
		                 not (List.Tot.mem (Cons?.hd s) (Cons?.tl s))))
let hd_unique #a #f s = set_props #a #f s

private val eq_helper: #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (let s = as_list s in Cons? s /\ f x (Cons?.hd s) /\ x =!= Cons?.hd s))
                       (ensures (not (mem #a #f x s)))
let eq_helper (#a:eqtype) #f x s = set_props #a #f s

let rec eq_lemma (#a:eqtype) #f s1 s2 = match s1, s2 with
  | [], []             -> ()
  | _::_, []           -> ()
  | [], _::_           -> ()
  | hd1::tl1, hd2::tl2 ->
    if hd1 = hd2 then
      //hd_unique calls help us prove that forall x. mem f x tl1 = mem f x tl2
      //so that we can apply IH
      (hd_unique #_ #f s1; hd_unique #_ #f s2; eq_lemma #_ #f tl1 tl2)
    else if f hd1 hd2 then
      eq_helper #_ #f hd1 s2
    else
      eq_helper #_ #f hd2 s1

let mem_empty #_ #_ _ = ()

let mem_singleton #_ #_ _ _ = ()

private val insert_mem: #a:eqtype -> #f:cmp a -> x:a -> y:a -> s:ordset a f
                -> Lemma (requires (True))
                         (ensures (mem #a #f y (insert' #a #f x s) =
                                   (x = y || mem #a #f y s)))
let rec insert_mem (#a:eqtype) #f x y s = match s with
  | []     -> ()
  | hd::tl ->
    if x = hd then ()
    else if f x hd then ()
    else insert_mem #_ #f x y tl

let rec mem_union #_ #f x s1 s2 = match s1 with
  | []     -> ()
  | hd::tl ->
    mem_union #_ #f x tl (insert' #_ #f hd s2); insert_mem #_ #f hd x s2

let rec mem_intersect #_ #f x s1 s2 = match s1 with
  | []     -> ()
  | hd::tl ->
    let _ = mem_intersect #_ #f x tl s2 in
    if mem #_ #f hd s2 then insert_mem #_ #f hd x (intersect #_ #f tl s2) else ()

private val subset_implies_mem:
  #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
  -> Lemma (requires (True))
          (ensures (subset #a #f s1 s2 ==> (forall x. mem #a #f x s1 ==>
                                                mem #a #f x s2)))
let rec subset_implies_mem (#a:eqtype) #f s1 s2 = match s1, s2 with
  | [], _          -> ()
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset_implies_mem #a #f tl tl'
    else subset_implies_mem #a #f s1 tl'
  | _, _           -> ()

private val mem_implies_subset:
  #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
  -> Lemma (requires (True))
          (ensures ((forall x. mem #a #f x s1 ==> mem #a #f x s2) ==> subset #a #f s1 s2))
let rec mem_implies_subset (#a:eqtype) #f s1 s2 = match s1, s2 with
  | [], [] -> ()
  | _::_, [] -> ()
  | [], _::_ -> ()
  | hd::tl, hd'::tl' ->
    set_props #a #f s1; set_props #a #f s2;

    if f hd hd' && hd = hd' then
      mem_implies_subset #a #f tl tl'
    else if f hd hd' && not (hd = hd') then
      ()
    else mem_implies_subset #a #f s1 tl'

let mem_subset (#a:eqtype) #f s1 s2 =
  subset_implies_mem #a #f s1 s2; mem_implies_subset #a #f s1 s2

let choose_empty (#a:eqtype) #f = ()

let choose_s (#a:eqtype) #f s =
  let Some e = choose #_ #f s in
  cut (equal #a #f s (insert' #a #f e (remove #a #f e s)))

let rec mem_remove (#a:eqtype) #f x y s = match s with
  | []     -> ()
  | hd::tl -> if y = hd then hd_unique #_ #f s else mem_remove #_ #f x y tl

let rec eq_remove (#a:eqtype) #f x s = match s with
  | []    -> ()
  | _::tl -> eq_remove #_ #f x tl

let size_empty (#a:eqtype) #f s = ()

let rec size_remove (#a:eqtype) #f x s = match s with
  | hd::tl ->
    if x = hd then () else size_remove #_ #f x tl

let size_singleton (#a:eqtype) #f x = ()

let rec subset_size (#a:eqtype) #f x y = match x, y with
  | [], _          -> ()
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset_size #a #f tl tl'
    else subset_size #a #f x tl'

(**********)

(* TODO:FIXME: implement *)
let size_union #a #f s1 s2 = admit ()

(**********)

let fold #a #acc #f g init s = List.Tot.fold_left g init s

private
let rec map_internal (#a #b:eqtype) (#fa:cmp a) (#fb:cmp b) (g:a -> b) (sa:ordset a fa)
  : Pure (ordset b fb)
    (requires (forall x y. x `fa` y ==> g x `fb` g y))
    (ensures (fun sb -> let sa = as_list sa in let sb = as_list sb in Cons? sb ==> Cons? sa /\ Cons?.hd sb == g (Cons?.hd sa)))
= match sa with
  | [] -> []
  | x :: xs ->
    let y = g x in
    let ys = map_internal #a #b #fa #fb g xs in
    if not (Cons? ys) || Cons?.hd ys <> y then
      y :: ys
    else ys

let map #a #b #fa #fb g sa = map_internal #a #b #fa #fb g sa

let lemma_strict_subset_size #a #f s1 s2 = admit ()

let lemma_minus_mem #a #f s1 s2 x = admit ()

let lemma_strict_subset_minus_size #a #f s1 s2 s = admit ()

let lemma_disjoint_union_subset #a #f s1 s2 = admit ()

let lemma_subset_union #a #f s1 s2 s = admit ()

let lemma_strict_subset_transitive #a #f s1 s2 s3 = admit ()

let lemma_intersect_symmetric #a #f s1 s2 = admit ()

let lemma_intersect_union_empty #a #f s1 s2 s3 = admit ()

let lemma_intersect_union_empty' #a #f s1 s2 s3 = admit ()

let union_comm #a #f s1 s2 = admit ()

let union_of_disj #a #f s1 s2 = admit ()

(* Conversion from OrdSet to Set *)

module S = FStar.Set

let rec as_set #a #f s = 
  match s with
  | []     -> S.empty
  | hd::tl -> S.union (S.singleton hd) (as_set #a #f tl)

let rec lemma_as_set_mem #a #f s x
  = match s with
    | []     -> ()
    | hd::tl -> 
        if x = hd 
        then ()
        else lemma_as_set_mem #a #f tl x

let rec lemma_as_set_disjoint #a #f s1 s2
  = match s1 with
    | []     -> ()
    | hd::tl ->
        if mem hd s2
        then assert (S.mem hd (as_set s2))
        else lemma_as_set_disjoint tl s2
