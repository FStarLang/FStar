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

val as_list (#a:eqtype) (#f:cmp a) (s:ordset a f) : Tot (l:list a{sorted f l})
let as_list #_ #_ s = s

let empty #_ #_ = []

let mem #_ #_ x s = List.Tot.mem x s

val insert': #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
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

val remove': #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
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
  : z:(ordset a f * bool) { (size (fst z) <= size s) &&
                            not(mem x (fst z)) &&
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


let mem_of_empty #a #f (s: ordset a f{size s = 0}) (x: a)
  : Lemma (not (mem x s)) = ()

let rec mem_implies_f #a #f (s: ordset a f) (x:a)
  : Lemma (requires mem x s) (ensures f (Cons?.hd s) x) = 
  match s with 
  | [] -> ()
  | h::t -> if size s > 0 && x <> h then mem_implies_f #a #f t x

let mem_of_tail #a #f (s: ordset a f{size s > 0}) (x:a)
  : Lemma ((mem #a #f x (Cons?.tl s) || (x = Cons?.hd s)) = mem x s) = ()

let not_mem_of_tail #a #f (s: ordset a f{size s > 0}) (x:a)
  : Lemma ((not (mem #a #f x (Cons?.tl s))) = (not (mem x s) || (x = Cons?.hd s))) = 
 match s with
 | h::[] -> ()
 | h::g::t -> if x = h then Classical.move_requires (mem_implies_f #a #f (g::t)) x 
           else mem_of_tail s x 

(* 
   Smart intersect is the set intersect that accounts for the ordering of both lists,
   eliminating some checks by trimming leading elements of one of the input lists 
   that are guaranteeed to not belong to the other list.
   E.g. smart_intersect [1;2;3] [3;4;5] can safely trim [1;2;3] to just [3]
   upon inspecting the head of [3;4;5]. 
*)
let rec smart_intersect #a #f (s1 s2: ordset a f) : Tot (z:ordset a f{
    (forall x. mem x z = (mem x s1 && mem x s2)) /\
    (forall (x:a{sorted f (x::s1)}). sorted f (x::z)) /\
    (forall (x:a{sorted f (x::s2)}). sorted f (x::z)) 
  }) (decreases size s1 + size s2) = 
  match s1 with 
  | [] -> []
  | h1::(t1:ordset a f) -> match s2 with
    | [] -> []
    | h2::(t2:ordset a f) -> 
      if h1=h2 then h1::smart_intersect t1 t2 
      else begin 
        if f h1 h2 then ( 
          let skip1, found = remove_until_greater_than #a #f h2 t1 in
          let subresult : ordset a f = smart_intersect skip1 t2 in 
          Classical.forall_intro (remove_until_gt_mem t1 h2);
          Classical.forall_intro (Classical.move_requires (mem_implies_f s2));
          if found then h2::subresult else subresult
        ) else (
          let skip2, found = remove_until_greater_than #a #f h1 t2 in
          let subresult = smart_intersect #a #f t1 skip2 in
          Classical.forall_intro (remove_until_gt_mem t2 h1);
          Classical.forall_intro (Classical.move_requires (mem_implies_f s1));
          if found then  h1::subresult 
          else subresult
        )
      end

val set_props_aux:
  #a:eqtype -> #f:cmp a -> s:ordset a f{Cons? (as_list s)}
  -> Lemma (requires True)
          (ensures  (let s = as_list s in
	             (forall x. List.Tot.mem x (Cons?.tl s) ==> (f (Cons?.hd s) x /\ Cons?.hd s =!= x))))
                     
let rec set_props_aux (#a:eqtype) #f s = match s with
  | x::tl -> if tl = [] then () else set_props_aux #a #f tl

let rec same_members_means_eq #a #f (s1 s2: ordset a f)
  : Lemma (requires forall x. mem x s1 = mem x s2) (ensures s1 == s2) = 
  match s1 with
  | [] -> if size s2>0 then assert (mem #a #f (Cons?.hd s2) s2) 
  | h1::t1 -> set_props_aux s1;
            set_props_aux s2;
            match s2 with 
            | h2::t2 -> same_members_means_eq #a #f t1 t2 

let intersect_sym #a #f (s1 s2: ordset a f) 
  : Lemma (smart_intersect s1 s2 = smart_intersect s2 s1) = 
  same_members_means_eq (smart_intersect s1 s2) (smart_intersect s2 s1)

let remove_until_gt_exclusion #a #f (s:ordset a f) (x:a) (test:a)
  : Lemma (requires f x test && (not (mem test (fst (remove_until_greater_than x s)))))
          (ensures x=test || not (mem test s)) = 
  remove_until_gt_mem s x test 
    
let rec remove_le_removes_x #a #f x (s:ordset a f)
  : Lemma (not (mem x (fst (remove_until_greater_than x s)))) = 
  match s with
  | y::ys -> remove_le_removes_x #a #f x ys
  | [] -> ()


val mem_implies_subset_aux:
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

val subset_implies_mem_aux:
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


let head_is_never_in_tail #a #f (s:ordset a f{size s > 0}) 
  : Lemma (not (mem #a #f (Cons?.hd s) (Cons?.tl s))) = set_props_aux s

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

val set_props:
  #a:eqtype -> #f:cmp a -> s:ordset a f{Cons? (as_list s)}
  -> Lemma (requires True)
          (ensures  (let s = as_list s in
	             (forall x. List.Tot.mem x (Cons?.tl s) ==> (f (Cons?.hd s) x /\ Cons?.hd s =!= x))))
let rec set_props (#a:eqtype) #f s = match s with
  | x::tl -> if tl = [] then () else set_props #a #f tl

val hd_unique: #a:eqtype -> #f:cmp a -> s:ordset a f
               -> Lemma (requires (Cons? (as_list s)))
                       (ensures (let s = as_list s in
		                 not (List.Tot.mem (Cons?.hd s) (Cons?.tl s))))
let hd_unique #a #f s = set_props #a #f s

val eq_helper: #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
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

val insert_mem: #a:eqtype -> #f:cmp a -> x:a -> y:a -> s:ordset a f
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

val subset_implies_mem:
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

val mem_implies_subset:
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
 
let me_empty (#a:eqtype) (#f:cmp a) (x:a) (s1 s2:ordset a f)
  : Lemma (requires sorted f (x::s1) /\ sorted f (x::s2) /\ s2=empty) 
          (ensures s1 = (minus s1 s2)) = ()

let minus_empty (#a:eqtype) #f (s1 s2: ordset a f) : Lemma (requires s2=empty) (ensures minus s1 s2 = s1) = ()
    
let lemma_minus_mem #a #f s1 s2 x = ()


let rec strict_subset_implies_diff_element #a #f (s1 s2: ordset a f) 
  : Lemma (requires strict_subset s1 s2)
          (ensures exists x. (mem x s2 /\ not (mem x s1))) = 
  match s1,s2 with
  | [], h::t -> ()
  | h1::t1, h2::t2 -> if h1<>h2 then (
                     if f h2 h1 then Classical.move_requires (mem_implies_f s1) h2 
                   ) else begin
                     strict_subset_implies_diff_element #a #f t1 t2; 
                     not_mem_of_tail s2 h1 
                   end

let diff_element_implies_strict_subset #a #f (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2 /\ (exists x. (mem x s2 /\ not (mem x s1))))
          (ensures strict_subset s1 s2) = ()

let diff_element_equals_strict_subset #a #f (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2)
          (ensures (strict_subset s1 s2) <==> (exists x. (mem x s2 /\ not (mem x s1)))) 
  = Classical.move_requires_2 strict_subset_implies_diff_element s1 s2

let rec count #a #f (s: ordset a f) (condition: a -> bool) : nat = 
  match s with
  | [] -> 0
  | h::t -> if condition h 
          then 1 + count #a #f t condition 
          else count #a #f t condition

let rec count_of_impossible_is_zero #a #f (s:ordset a f) (condition: a -> bool {forall p. not (condition p)}) : Lemma (count s condition = 0) = 
  match s with 
  | [] -> ()
  | h::t -> count_of_impossible_is_zero #a #f t condition 

let rec count_all #a #f (s: ordset a f) : Lemma (count s (fun x -> true) = size s) = 
  match s with
  | [] -> ()
  | h::t -> count_all #a #f t

let intersect_with_empty #a #f (s: ordset a f) 
  : Lemma (smart_intersect s [] = [] /\ smart_intersect [] s = []) = ()

let size_of_tail #a #f (s:ordset a f) 
  : Lemma (requires size s > 0)
          (ensures size s = 1 + (size #a #f (Cons?.tl s))) = ()

let count_of_empty #a #f (s: ordset a f) 
  : Lemma (requires size s = 0) (ensures forall (c: a -> bool). count s c = 0) = () 

let count_of_tail #a #f (s: ordset a f{size s > 0}) (r: ordset a f{size r > 0})
  : Lemma (requires Cons?.hd s = Cons?.hd r)
          (ensures count s (fun x -> mem x r) = 1 + count #a #f (Cons?.tl s) (fun x -> mem x r)) = () 

let rec where #a #f (s: ordset a f) (cond: a -> bool) 
  : Pure (ordset a f) 
         (requires True)
         (ensures fun (z:ordset a f) -> 
           (forall x. mem x z = (mem x s && cond x)) /\
           (if size z > 0 && size s > 0 then f (Cons?.hd s) (Cons?.hd z) else true) )= 
  match s with
  | [] -> []
  | h::[] -> if cond h then [h] else []
  | h::g::[] -> if cond h then h::(where #a #f [g] cond) else where #a #f [g] cond
  | h::g::(t:ordset a f) -> if cond h then h::(where #a #f (g::t) cond) else where (g::t) cond 

let intersect_eq_where #a #f (s1 s2: ordset a f)
  : Lemma (smart_intersect s1 s2 = where s1 (fun x -> mem x s2)) = 
  let rhs = where s1 (fun x -> mem x s2) in
  let lhs = smart_intersect s1 s2 in
  assert (forall x. mem x rhs = (mem x s1 && mem x s2)); 
  assert (forall x. mem x lhs = (mem x s1 && mem x s2));
  same_members_means_eq lhs rhs

let minus_eq_where #a #f (s1 s2: ordset a f)
  : Lemma (smart_minus s1 s2 = where s1 (fun x -> not (mem x s2))) = 
  let rhs = where s1 (fun x -> not (mem x s2)) in
  let lhs = smart_minus s1 s2 in
  assert (forall x. mem x rhs = (mem x s1 && not (mem x s2))); 
  assert (forall x. mem x lhs = (mem x s1 && not (mem x s2)));
  same_members_means_eq lhs rhs  

let rec count_is_size_of_where #a #f (s: ordset a f) (cond: a -> bool)
  : Lemma (count s cond = size (where s cond)) = 
  match s with
  | [] -> ()
  | h::t -> count_is_size_of_where #a #f t cond

let size_of_intersect #a #f (s1 s2: ordset a f)
  : Lemma (ensures size (smart_intersect s1 s2) = count s1 (fun x -> mem x s2) /\
                   size (smart_intersect s1 s2) = count s2 (fun x -> mem x s1))
          (decreases size s1 + size s2) =   
  intersect_eq_where s1 s2;
  intersect_eq_where s2 s1;
  intersect_sym s1 s2;
  count_is_size_of_where s1 (fun x -> mem x s2);   
  count_is_size_of_where s2 (fun x -> mem x s1)
  
let count_of_intersect #a #f (s1 s2: ordset a f) 
  : Lemma (count s1 (fun x -> mem x s2) = count s2 (fun x -> mem x s1)) = size_of_intersect s1 s2

let union_mem_forall #a #f (s1 s2: ordset a f)
  : Lemma (forall x. (mem x (union s1 s2)) = (mem x s1 || mem x s2)) =
  let aux x : Lemma (mem x (union s1 s2) = (mem x s1 || mem x s2)) =   
    mem_union x s1 s2 in Classical.forall_intro aux  

let union_with_empty #a #f (s: ordset a f)
  : Lemma (union s empty = s) = 
  let aux x : Lemma (mem x (union s empty) = mem x s) =   
    mem_union x s empty in
  Classical.forall_intro aux;
  eq_lemma (union s empty) s

let union_head_lemma #a #f (s1 s2: ordset a f)
  : Lemma (match s1, s2 with 
           | [],[] -> (union s1 s2 = [])
           | [],h::t -> size (union s1 s2) > 0 && Cons?.hd (union s1 s2) = h
           | h::t,[] -> size (union s1 s2) > 0 && Cons?.hd (union s1 s2) = h
           | h1::t1, h2::t2 -> size (union s1 s2) > 0 && 
                            (Cons?.hd (union s1 s2) = (if f h1 h2 then h1 else h2))                             
                            ) = 
  match s1,s2 with
  | [],[] -> ()
  | [],h::t -> ()
  | h::t,[] -> union_with_empty s1
  | h1::t1, h2::t2 -> union_mem_forall s1 s2;
                   set_props s1;
                   set_props s2;
                   set_props (union s1 s2)
           
let union_sort_lemma (#a:eqtype) #f (h:a) (t1 t2: ordset a f)
  : Lemma (requires sorted f (h::t1) /\ sorted f (h::t2))
          (ensures sorted f (h::(union t1 t2))) = 
  if size t1 = 0 then union_with_empty t2
  else if size t2 = 0 then union_with_empty t1 
  else begin 
    union_mem_forall t1 t2;
    set_props t1;
    set_props t2;
    set_props (union t1 t2)    
  end

let union_with_prefix (#a:eqtype) #f (h:a) (t1 t2: (z:ordset a f{sorted f (h::z)}))
  : Lemma (union #a #f (h::t1) (h::t2) = h::(union t1 t2)) = 
  union_mem_forall t1 t2;
  union_sort_lemma h t1 t2;
  same_members_means_eq (union #a #f (h::t1) (h::t2)) (h::(union t1 t2))

let union_of_tails_size (#a:eqtype) #f (s1 s2: ordset a f)
  : Lemma (requires size s1 > 0 && size s2 > 0 && (Cons?.hd s1 <> Cons?.hd s2) && f (Cons?.hd s1) (Cons?.hd s2))
          (ensures size (union s1 s2) = 1 + size (union #a #f (Cons?.tl s1) s2)) = 
  match s1 with | h1::(t1:ordset a f) -> match s2 with | h2::(t2:ordset a f) ->
    union_mem_forall t1 s2;
    set_props s1;
    set_props s2;
    same_members_means_eq (h1::(union t1 s2)) (union s1 s2)

#push-options "--z3rlimit 10"
let rec size_of_union #a #f (s1 s2: ordset a f)
  : Lemma (ensures size (union s1 s2) = size s1 + size s2 - (size (smart_intersect s1 s2)))
          (decreases size s1 + size s2) = 
  let size = size #a #f in
  match s1,s2 with
  | [], _ -> union_mem_forall s1 s2;
            same_members_means_eq s2 (union s1 s2)
  | _, [] -> union_mem_forall s1 s2;
            same_members_means_eq s1 (union s1 s2)
  | h1::(t1:ordset a f), h2::(t2:ordset a f) -> size_of_union #a #f t1 t2;
                   assert (size (union t1 t2) = size t1 + size t2 - size (smart_intersect t1 t2));
                   if h1 = h2 then begin
                     union_with_prefix h1 t1 t2;
//                     assert (union s1 s2 = (h1::(union t1 t2)));
//                     assert (size (union s1 s2) = 1 + size (union t1 t2));
//                     assert (size t1 = size s1 - 1);
//                     assert (size t2 = size s2 - 1);
//                     assert (size (smart_intersect t1 t2) + 1 = size (smart_intersect s1 s2));
                     ()
                     same_members_means_eq (smart_intersect s1 s2) (smart_intersect t1 s2)
                   end else begin
                     if f h1 h2 then begin
                       size_of_union t1 s2;
//                       assert (size (union t1 s2) = size t1 + size s2 - size (smart_intersect t1 s2));
                       union_of_tails_size s1 s2;
//                       assert (size (union s1 s2) = 1 + size (union t1 s2));
                       Classical.move_requires (mem_implies_f s2) h1;
//                       assert (not (mem h1 s2));
                       // step by damned step.
//                       assert (size (union s1 s2) = 1 + size t1 + size s2 - size (smart_intersect t1 s2));
//                       assert (size (union s1 s2) = size s1 + size s2 - size (smart_intersect t1 s2));
//                      assert (size (union s1 s2) = size s1 + size s2 - size (smart_intersect s1 s2));
                       ()
                     end else begin
                       size_of_union s1 t2;
                       intersect_sym s1 t2;
                       union_of_tails_size s2 s1; 
                     end
                   end
                     same_members_means_eq (union s1 s2) (union s2 s1);
                     same_members_means_eq (union s1 t2) (union t2 s1); 
                     same_members_means_eq (smart_intersect s1 s2) (smart_intersect t2 s1)
#pop-options

let rec count_dichotomy #a #f (s: ordset a f) (cond: a -> bool)
  : Lemma (size s = count s cond + count s (fun x -> not (cond x))) = 
  match s with
  | [] -> ()
  | h::t -> count_dichotomy #a #f t cond

let size_of_minus #a #f (s1 s2: ordset a f)
  : Lemma (size (smart_minus s1 s2) = size s1 - size (smart_intersect s1 s2)) = 
  minus_eq_where s1 s2;
  intersect_eq_where s1 s2;
  let mem_of_s2 x = mem x s2 in
  let not_mem_of_s2 x = not (mem x s2) in
  count_dichotomy s1 mem_of_s2;
  assert ((size s1) = (count s1 mem_of_s2) + (count s1 not_mem_of_s2));
  count_is_size_of_where s1 mem_of_s2;
  count_is_size_of_where s1 not_mem_of_s2


let intersect_with_subset #a #f (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2)
          (ensures smart_intersect s1 s2 = s1) = 

//(ensures  (size (minus s s2) < size (minus s s1)))
  same_members_means_eq (smart_intersect s1 s2) s1
let lemma_strict_subset_minus_size #a #f s1 s2 s = 
  let size_diff : pos = size s2 - size s1 in
  size_of_minus s2 s1;
  size_of_minus s s2;
  size_of_minus s s1;
  intersect_with_subset s2 s;
  intersect_sym s2 s;
  intersect_with_subset s1 s;
  intersect_sym s1 s

let lemma_disjoint_union_subset #a #f s1 s2 = size_of_union s1 s2

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
