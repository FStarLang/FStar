(*
   Copyright 2008-2022 Microsoft Research

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
  | y :: ys -> if f x y && x <> y
             then s
             else remove_le #a #f x ys

let rec not_mem_aux #a #f x (s:ordset a f)
  : Lemma (requires (size s > 0) && (Cons?.hd s <> x) && (f x (Cons?.hd s)))
          (ensures not (mem x s))
          = 
  match s with  
  | h::t -> if t = [] then () else not_mem_aux #a #f x t 

let rec tail_is_subset #a #f (s:ordset a f{size s > 0})
  : Lemma (Cons?.tl s `subset` s) = 
  match s with
  | [] -> ()
  | h::(t:ordset a f) -> if size t > 0 then tail_is_subset #a #f t

let rec self_is_subset #a #f (s:ordset a f)
  : Lemma (subset s s) = match s with 
  | [] -> ()
  | h::(t:ordset a f) -> self_is_subset t

let rec remove_until_greater_than #a #f x (s: ordset a f)
  : z:(ordset a f * bool) { not(mem x (fst z)) &&
                            (subset (fst z) s) &&
                            (snd z = mem x s) &&
                            (match (fst z) with 
                            | [] -> true
                            | h::t -> (sorted f (x::(fst z)))) } =
  match s with
  | [] -> ([], false)
  | h::(t:ordset a f) -> if h=x then (
                        assert (sorted f t);   
                        if size t > 0 then not_mem_aux x t;
                        tail_is_subset s;
                        (t, true)
                      )
          else if f x h then (
            not_mem_aux x s;
            self_is_subset s;
            (s, false)
          )
          else remove_until_greater_than x t

let rec remove_until_gt_prop #a #f (s: ordset a f) (x:a) (test:a)
  : Lemma (f test x ==> not (mem test (fst (remove_until_greater_than x s)))) = 
  match s with
  | [] -> ()
  | h::(t:ordset a f) -> 
          let aux (test:a) 
            : Lemma (requires f test x && h<>test) 
                    (ensures not (mem test (fst (remove_until_greater_than x s)))) =
            remove_until_gt_prop #a #f t x test;
            () in Classical.move_requires aux test;
          if h <> x then remove_until_gt_prop t x test

let rec remove_until_gt_mem #a #f (s: ordset a f) (x:a) (test:a)
  : Lemma (mem test (fst (remove_until_greater_than x s)) = (
             mem test s &&
             f x test &&
             (x<>test)
           )) = 
  match s with
  | [] -> ()
  | h::(t:ordset a f) -> remove_until_gt_prop s x test;
                       remove_until_gt_mem t x test

let remove_until_gt_exclusion #a #f (s:ordset a f) (x:a) (test:a)
  : Lemma (requires f x test && (not (mem test (fst (remove_until_greater_than x s)))))
          (ensures x=test || not (mem test s)) = 
  remove_until_gt_mem s x test 
    
private let rec remove_le_removes_x #a #f x (s:ordset a f)
  : Lemma (not (mem x (fst (remove_until_greater_than x s)))) = 
  match s with
  | y::ys -> remove_le_removes_x #a #f x ys
  | [] -> ()

private val set_props_aux:
  #a:eqtype -> #f:cmp a -> s:ordset a f{Cons? (as_list s)}
  -> Lemma (requires True)
          (ensures  (let s = as_list s in
	             (forall x. List.Tot.mem x (Cons?.tl s) ==> (f (Cons?.hd s) x /\ Cons?.hd s =!= x))))
                     
let rec set_props_aux (#a:eqtype) #f s = match s with
  | x::tl -> if tl = [] then () else set_props_aux #a #f tl


private val mem_implies_subset_aux:
  #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
  -> Lemma (requires (True))
          (ensures ((forall x. mem #a #f x s1 ==> mem #a #f x s2) ==> subset #a #f s1 s2))
          
let rec mem_implies_subset_aux (#a:eqtype) #f s1 s2 = match s1, s2 with
  | [], [] -> ()
  | _::_, [] -> ()
  | [], _::_ -> ()
  | hd::tl, hd'::tl' ->
    set_props_aux #a #f s1; set_props_aux #a #f s2;

    if f hd hd' && hd = hd' then
      mem_implies_subset_aux #a #f tl tl'
    else if f hd hd' && not (hd = hd') then
      ()
    else mem_implies_subset_aux #a #f s1 tl'

private val subset_implies_mem_aux:
  #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
  -> Lemma (requires (True))
          (ensures (subset #a #f s1 s2 ==> (forall x. mem #a #f x s1 ==>
                                                mem #a #f x s2)))
let rec subset_implies_mem_aux (#a:eqtype) #f s1 s2 = match s1, s2 with
  | [], _          -> ()
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset_implies_mem_aux #a #f tl tl'
    else subset_implies_mem_aux #a #f s1 tl'
  | _, _           -> ()

let subset_transitivity #a #f (p q r: ordset a f)
  : Lemma (requires p `subset` q /\ q `subset` r)
          (ensures p `subset` r) = 
  subset_implies_mem_aux p q;
  subset_implies_mem_aux q r;
  mem_implies_subset_aux p r

let rec mem_implies_f #a #f (s: ordset a f) (x:a)
  : Lemma (requires mem x s) (ensures f (Cons?.hd s) x) = 
  match s with 
  | [] -> ()
  | h::t -> if size s > 0 && x <> h then mem_implies_f #a #f t x

let head_is_never_in_tail #a #f (s:ordset a f{size s > 0}) 
  : Lemma (not (mem #a #f (Cons?.hd s) (Cons?.tl s))) = set_props_aux s

let mem_of_empty #a #f (s: ordset a f{size s = 0}) (x: a)
  : Lemma (not (mem x s)) = ()

let rec smart_minus #a #f (p q: ordset a f) 
  : z:ordset a f { ( forall x. mem x z = (mem x p && (not (mem x q)))) /\
                   (match p,z with 
                    | ph::pt, zh::zt -> f ph zh
                    | ph::pt, [] -> subset p q
                    | [], _ -> z = [])
                 } =
  match p with
  | [] -> []
  | ph::(pt:ordset a f) -> match q with
    | [] -> p
    | qh::(qt:ordset a f) -> 
      let q_after_ph, found = remove_until_greater_than ph q in  
      Classical.forall_intro (remove_until_gt_mem q ph);   
      Classical.forall_intro (Classical.move_requires (mem_implies_f p));  
      if found then begin
        let result = smart_minus pt q_after_ph in
        set_props_aux p;
        if result = [] then begin
          subset_transitivity pt q_after_ph q;
          subset_implies_mem_aux pt q;          
          mem_implies_subset_aux p q
        end;
        result
      end
      else ph::(smart_minus pt q_after_ph)      

let minus_empty_means_subset #a #f (p q: ordset a f)
  : Lemma (requires size (smart_minus p q) = 0) (ensures subset p q) = ()

let ncmp (x y:nat) = x <= y

let _ = assert (smart_minus #nat #ncmp [1;2;3;4] [3] == [1;2;4])
  
let minus #a #f s1 s2 = smart_minus s1 s2 

let rec remove_le_never_increases_size #a #f (s: ordset a f) (x:a)
  : Lemma (size (remove_le x s) <= size s) = 
  match s with
  | [] -> ()
  | h::t -> remove_le_never_increases_size #a #f t x

let rec remove_le_decreases_size #a #f (s: ordset a f) (x:a)
  : Lemma (requires mem x s) (ensures size (remove_le x s) < size s) = 
  match s with
  | [] -> ()
  | h::t -> if x=h then () else remove_le_decreases_size #a #f t x
    

let minus_removes_s2 #a #f (p q: ordset a f) (x:a)
  : Lemma (ensures mem x q ==> not (mem x (minus p q))) = ()
           
let minus_removes_all_of_s2 #a #f (s1 s2: ordset a f) (x:a{mem x s2})
  : Lemma (not (mem x (minus s1 s2))) = ()  

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

let singleton_union_sym (#a:eqtype) #f (s: ordset a f) (x:a) 
  : Lemma (ensures union s [x] == union [x] s)
          (decreases s) = eq_lemma (union s [x]) (union [x] s)

let rec insert_when_already_exists (#a:eqtype) #f (s: ordset a f) (x:a)
  : Lemma (requires mem x s) (ensures insert' x s == s) = 
  match s with
  | h::t -> if h<>x then insert_when_already_exists #a #f t x
  | [] -> ()

let rec size_insert (#a:eqtype) #f (s: ordset a f) (x:a)
  : Lemma (size (insert' x s) >= size s) = 
  match s with 
  | h::t -> size_insert #a #f t x
  | [] -> ()

let rec precise_size_insert (#a:eqtype) #f (s: ordset a f) (x:a)
  : Lemma (ensures size (insert' x s) = (if mem x s then size s else (size s) + 1)) = 
  match s with
  | h::t -> precise_size_insert #a #f t x
  | [] -> ()
       
let rec size_of_union_left (#a:eqtype) #f (s1 s2: ordset a f)
  : Lemma (ensures size (union s1 s2) >= size s2) =
  match s1 with
  | [] -> ()
  | hd::tl -> size_of_union_left #a #f tl (insert' hd s2);
            precise_size_insert s2 hd;
            if mem hd s2 then insert_when_already_exists s2 hd 

let size_of_union_right (#a:eqtype) #f (s1 s2: ordset a f)
  : Lemma (ensures size (union s1 s2) >= size s1) =
  eq_lemma (union s1 s2) (union s2 s1);
  size_of_union_left s2 s1

let size_union #a #f s1 s2 =
  size_of_union_left s1 s2;
  size_of_union_right s1 s2

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

let lemma_strict_subset_size #a #f s1 s2 = 
  let eql (p q: ordset a f) 
    : Lemma (requires forall x. mem x p = mem x q) 
            (ensures p=q) 
    = eq_lemma p q in 
  Classical.move_requires_2 eql s1 s2;
  eliminate exists x. mem x s2 && not (mem x s1) 
  returns size s2 > size s1 with _.
  begin
    let ins_mem x s p // perhaps we should reorder parameters of insert_mem...
      : Lemma(mem p (insert' #a #f x s) = (p=x || mem p s)) 
      = insert_mem #a #f x p s in
    Classical.forall_intro (ins_mem x s1);
    precise_size_insert s1 x;
    assert (subset (insert' x s1) s2)
  end

let aux_lemma_remove (#a:eqtype) #f (s: ordset a f) (x:a) (test:a)
  : Lemma (mem test (remove x s) = (mem test s && not (x=test))) = ()

let remove_le_empty #a #f x (s:ordset a f) : Lemma (requires s = empty) (ensures remove_le #a #f x s = empty) = ()
 
private let me_empty (#a:eqtype) (#f:cmp a) (x:a) (s1 s2:ordset a f)
  : Lemma (requires sorted f (x::s1) /\ sorted f (x::s2) /\ s2=empty) 
          (ensures s1 = (minus s1 s2)) = ()

let minus_empty (#a:eqtype) #f (s1 s2: ordset a f) : Lemma (requires s2=empty) (ensures minus s1 s2 = s1) = ()
    
let lemma_minus_mem #a #f s1 s2 x = ()
 
let lemma_strict_subset_minus_size #a #f s1 s2 s = admit() 

let lemma_disjoint_union_subset #a #f s1 s2 = admit ()

let lemma_subset_union #a #f s1 s2 s = ()

let lemma_strict_subset_transitive #a #f s1 s2 s3 = ()

let lemma_intersect_symmetric #a #f s1 s2 = eq_lemma (intersect s1 s2) (intersect s2 s1)

let lemma_intersect_union_empty #a #f s1 s2 s3 = eq_lemma empty (intersect (union s1 s2) s3)

let lemma_intersect_union_empty' #a #f s1 s2 s3 = eq_lemma empty (intersect s1 s3);
                                                  eq_lemma empty (intersect s2 s3) 

let union_comm #a #f s1 s2 = eq_lemma (union s1 s2) (union s2 s1)

let union_of_disj #a #f s1 s2 = 
  let aux x : Lemma (mem x (minus (union s1 s2) s1) = (mem x s2)) 
    = mem_intersect x s1 s2 in Classical.forall_intro aux;
  eq_lemma (minus (union s1 s2) s1) s2

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
