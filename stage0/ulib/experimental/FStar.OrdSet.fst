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

[@@do_not_unrefine]
type ordset a f = l:(list a){sorted f l}

let hasEq_ordset _ _ = ()
    
let rec simple_induction #t #f (p: ordset t f -> Type0) (x: ordset t f)
  : Lemma (requires p [] /\ (forall (l: ordset t f{Cons? l}). p (Cons?.tl l) ==> p l))
          (ensures p x) = match x with
  | [] -> ()
  | ph::pt -> simple_induction p pt;
            assert (p (Cons?.tl (ph::pt)))
  
let rec base_induction #t #f (p: ordset t f -> Type0) (x: ordset t f)
  : Lemma (requires (forall (l: ordset t f{List.Tot.Base.length l < 2}). p l) 
                  /\ (forall (l: ordset t f{Cons? l}). p (Cons?.tl l) ==> p l))
          (ensures p x) 
          (decreases List.Tot.Base.length x) = 
  if List.Tot.Base.length x < 2 then ()
  else match x with
  | ph::pt -> base_induction p pt;
            assert (p (Cons?.tl (ph::pt)))
            
let empty #_ #_ = []

let tail #a #f s = Cons?.tl s <: ordset a f 
let head #_ #_ s = Cons?.hd s

let mem #_ #_ x s = List.Tot.mem x s
 
(* In case snoc-based List implementation is optimized, we use library ones,
   but we additionally supply them with relevant postconditions that come 
   from s being an ordset. *)
let rec last_direct #a #f (s: ordset a f{s <> empty}) 
  : (x:a{mem x s /\ (forall (z:a{mem z s}). f z x)}) 
  = match s with
  | [x] -> x  
  | h::g::t -> last_direct (tail s)

let last_lib #a #f (s: ordset a f{s <> empty}) 
  = snd (List.Tot.Base.unsnoc s)

let last_eq #a #f (s: ordset a f{s <> empty}) 
  : Lemma (last_direct s = last_lib s) = simple_induction 
    (fun p -> if p<>[] then last_direct #a #f p = last_lib p else true) s

let last #a #f s = last_eq s; last_lib s

let rec liat_direct #a #f (s: ordset a f{s <> empty}) : (l:ordset a f{
    (forall x. mem x l = (mem x s && (x <> last s))) /\
    (if tail s <> empty then head s = head l else true)
  }) =  
  match s with
  | [x] -> []
  | h::g::t -> h::(liat_direct #a #f (g::t))

let liat_lib #a #f (s: ordset a f{s <> empty}) = fst (List.Tot.Base.unsnoc s)

let liat_eq #a #f (s:ordset a f {s<>empty})
  : Lemma (liat_direct s = liat_lib s) = simple_induction
    (fun p -> if p<>[] then liat_direct p = liat_lib p else true) s

let liat #a #f s = liat_eq s; liat_lib s
 
let unsnoc #a #f s = 
  liat_eq s;
  last_eq s;
  let l = List.Tot.Base.unsnoc s in
  (fst l, snd l)

let as_list (#a:eqtype) (#f:cmp a) (s:ordset a f) : Tot (l:list a{sorted f l}) = s

val insert': #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){let s = as_list s in let l = as_list l in
	                           (Cons? l /\
                                    (head #a #f l = x \/
                                    (Cons? s /\ head #a #f l = head #a #f s)))})
let rec insert' #_ #f x s =
  match s with
  | []     -> [x]
  | hd::tl ->
    if x = hd then hd::tl
    else if f x hd then x::hd::tl
    else hd::(insert' #_ #f x tl)

let rec distinct' #a f l : Tot (ordset a f) = 
  match l with 
  | []  -> []
  | x::t -> insert' x (distinct' f t)

let rec insert_mem (#a:eqtype) #f (x:a) (s:ordset a f) 
  : Lemma (mem x (insert' x s)) 
  = if s<>empty then insert_mem #a #f x (tail s)

let insert_sub (#a:eqtype) #f x (s:ordset a f) test
  : Lemma (mem test (insert' x s) = (mem test s || test = x)) = 
  simple_induction (fun p -> mem test (insert' x p) = (mem test p || test = x)) s

let rec distinct_props #a (f:cmp a) (l: list a) 
  : Lemma (forall x. (mem x (distinct' f l) = List.Tot.Base.mem x l)) = 
  match l with 
  | [] -> ()
  | x::t -> distinct_props f t;
          Classical.forall_intro (insert_sub x (distinct' f t))

let distinct #a f l = distinct_props f l; distinct' f l

let rec union #_ #_ s1 s2 = match s1 with
  | []     -> s2
  | hd::tl -> union tl (insert' hd s2) 

val remove': #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){ ((Nil? s ==> Nil? l) /\
                                    (Cons? s ==> head s = x ==> l = tail s) /\
                                    (Cons? s ==> head s =!= x ==> (Cons? l /\ head l = Cons?.hd s)))})
                                    
let rec remove' #a #f x s = match s with
  | [] -> []
  | hd::(tl: ordset a f) ->
    if x = hd then tl
    else hd::(remove' x tl)

let size' (#a:eqtype) (#f:cmp a) (s:ordset a f) = List.Tot.length s

let liat_length #a #f (s:ordset a f{s<>empty}) : Lemma (size' (liat s) = ((size' s) - 1)) 
  = simple_induction (fun p -> if p<>empty then size' (liat p) = ((size' p)-1) else true) s

let rec not_mem_aux (#a:eqtype) (#f:cmp a) (x:a) (s:ordset a f)
  : Lemma (requires (size' s > 0) && (head s <> x) && (f x (head s)))
          (ensures not (mem x s)) = 
  if tail s <> [] then not_mem_aux x (tail s)

let rec subset' #a #f (s1 s2: ordset a f) = match s1, s2 with
  | [], _          -> true
  | hd::tl, hd'::tl' -> if f hd hd' && hd = hd' then subset' #a #f tl tl'
                     else if f hd hd' && not (hd = hd') then false
                     else subset' #a #f s1 tl'
  | _, _           -> false
  
let tail_is_subset #a #f (s:ordset a f{size' s > 0})
  : Lemma (Cons?.tl s `subset'` s) = 
  simple_induction (fun (s:ordset a f) -> size' s=0 || subset' (Cons?.tl s) s) s
  
let self_is_subset #a #f (s:ordset a f)
  : Lemma (subset' s s) = simple_induction (fun (s:ordset a f) -> subset' s s) s

(* 
  returns a pair of (fst z) = (everything from s that goes after x)
  and (snd z) = (true if x was found in s, false otherwise)
*)
let rec remove_until_greater_than #a #f x (s: ordset a f)
  : z:(ordset a f & bool) { (size' (fst z) <= size' s) &&
                            (not(mem x (fst z))) &&
                            (subset' (fst z) s) &&
                            (snd z = mem x s) &&
                            (match (fst z) with 
                             | [] -> true
                             | h::t -> (sorted f (x::(fst z)))) 
                          } =
  match s with
  | [] -> ([], false)
  | h::(t:ordset a f) -> if h=x then begin
                         if size' t > 0 then not_mem_aux x t;
                         tail_is_subset s;
                         (t, true)
                       end
                       else if f x h then begin
                         not_mem_aux x s;
                         self_is_subset s;
                       (s, false)
                       end 
                       else remove_until_greater_than x t

let rec remove_until_gt_prop #a #f (s: ordset a f) (x:a) (test:a)
  : Lemma (f test x ==> not (mem test (fst (remove_until_greater_than x s)))) = 
  match s with
  | [] -> ()
  | h::(t:ordset a f) -> 
    let aux (test:a) : Lemma (requires f test x && h<>test) 
                             (ensures not (mem test (fst (remove_until_greater_than x s)))) =
      remove_until_gt_prop #a #f t x test 
    in Classical.move_requires aux test;
    if h <> x then remove_until_gt_prop t x test

let rec remove_until_gt_mem #a #f (s: ordset a f) (x:a) (test:a)
  : Lemma (mem test (fst (remove_until_greater_than x s)) = (
             mem test s &&
             f x test &&
             (x<>test)
           )) 
  = if size' s > 0 then remove_until_gt_mem (tail s) x test

let mem_implies_f #a #f (s: ordset a f) (x:a)
  : Lemma (requires mem x s) (ensures f (Cons?.hd s) x) 
  = simple_induction (fun s -> mem x s ==> f (head s) x) s
    
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
  }) (decreases size' s1 + size' s2) = 
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

let intersect #a #f s1 s2 = smart_intersect s1 s2

let choose #a #f s = match s with | [] -> None | x::_ -> Some x
  
let remove #a #f x s = remove' #_ #f x s

let size #a #f s = size' s

let subset #a #f s1 s2 = subset' s1 s2

let singleton (#a:eqtype) #f x = [x]

let mem_of_empty #a #f (s: ordset a f{size s = 0}) (x: a)
  : Lemma (not (mem x s)) = ()

let mem_of_tail #a #f (s: ordset a f{size s > 0}) (x:a)
  : Lemma ((mem #a #f x (Cons?.tl s) || (x = Cons?.hd s)) = mem x s) = ()

let not_mem_of_tail #a #f (s: ordset a f{size s > 0}) (x:a)
  : Lemma (not (mem x (tail s)) = not (mem x s) || x = head s) 
  = simple_induction (fun s -> mem x s ==> f (head s) x) s

let rec set_props #a #f (s:ordset a f) 
  : Lemma (if size s > 0 then ((forall x. mem x (tail s) ==> f (head s) x /\ head s <> x)) 
           else forall x. not (mem x s))
  = if (size s > 1) then set_props (tail s)

let rec same_members_means_eq #a #f (s1 s2: ordset a f)
  : Lemma (requires forall x. mem x s1 = mem x s2) (ensures s1 == s2) = 
  match s1 with
  | [] -> if size s2>0 then assert (mem (head s2) s2) 
  | h1::t1 -> set_props s1;
            set_props s2;
            match s2 with 
            | h2::t2 -> same_members_means_eq #a #f t1 t2 

let intersect_is_symmetric #a #f (s1 s2: ordset a f) 
  : Lemma (intersect s1 s2 = intersect s2 s1) 
  = same_members_means_eq (intersect s1 s2) (intersect s2 s1)

let remove_until_gt_exclusion #a #f (s:ordset a f) (x:a) (test:a)
  : Lemma (requires f x test && (not (mem test (fst (remove_until_greater_than x s)))))
          (ensures x=test || not (mem test s)) = 
  remove_until_gt_mem s x test 
      
let rec mem_implies_subset #a #f (s1 s2: ordset a f)
  : Lemma ((forall x. mem x s1 ==> mem x s2) ==> subset s1 s2)
  = match s1 with 
  | [] -> ()
  | h1::(t1:ordset a f) -> set_props s1;
                         set_props s2;
                         mem_implies_subset t1 s2;
                         if (size s2 > 0 && f (head s2) h1) 
                         then mem_implies_subset s1 (tail s2)

let rec subset_implies_mem #a #f (p q: ordset a f)
  : Lemma (subset p q ==> (forall x. mem x p ==> mem x q)) = 
 if Cons? p && Cons? q then 
   if head p = head q
   then subset_implies_mem (tail p) (tail q)
   else subset_implies_mem p (tail q)
 
let subset_transitivity #a #f (p q r: ordset a f)
  : Lemma (requires p `subset` q /\ q `subset` r)
          (ensures p `subset` r) = 
  subset_implies_mem p q;
  subset_implies_mem q r;
  mem_implies_subset p r

let head_is_never_in_tail #a #f (s:ordset a f{size s > 0}) 
  : Lemma (not (mem (head s) (tail s))) = set_props s

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
        set_props p;
        if result = [] then begin          
          subset_transitivity pt q_after_ph q;
          subset_implies_mem pt q;          
          mem_implies_subset p q
        end;
        result
      end
      else ph::(smart_minus pt q_after_ph)      

let empty_minus_means_subset #a #f (p q: ordset a f)
  : Lemma (requires size (smart_minus p q) = 0) (ensures subset p q) = ()

// a little test versus integers :)
let ncmp (x y:nat) = x <= y
let _ = assert (smart_minus #nat #ncmp [1;2;3;4] [3] == [1;2;4])
  
let minus #a #f s1 s2 = smart_minus s1 s2 

let strict_subset #a #f s1 s2 = s1 <> s2 && subset s1 s2

let eq_lemma #a #f s1 s2 = same_members_means_eq s1 s2

let mem_empty #_ #_ _ = ()

let mem_singleton #_ #_ _ _ = ()

let mem_insert (#a:eqtype) #f (el:a) (s: ordset a f) (x:a)
  : Lemma (mem x (insert' el s) = (x=el || mem x s)) = 
  simple_induction (fun p -> mem x (insert' el p) = (x=el || mem x p)) s
  
let rec mem_union #_ #_ s1 s2 x = 
  if size s1 > 0 then 
    match s1 with | hd::tl -> 
      mem_union tl (insert' hd s2) x;
      mem_insert hd s2 x

let mem_intersect #_ #f s1 s2 x = ()

let mem_subset (#a:eqtype) #f s1 s2 =
  subset_implies_mem s1 s2; 
  mem_implies_subset s1 s2

let choose_empty (#a:eqtype) #f = ()

let choose_s (#a:eqtype) #f s = () 

let rec mem_remove (#a:eqtype) #f x y s = 
  if size s > 0 then (set_props s; mem_remove x y (tail s))

let eq_remove (#a:eqtype) #f x s 
  = simple_induction (fun p -> not (mem x p) ==> p = remove x p) s

let size_empty (#a:eqtype) #f s = ()

let rec size_remove (#a:eqtype) #f x s = match s with
  | hd::tl -> if x<>hd then size_remove #_ #f x tl

let size_singleton (#a:eqtype) #f x = ()

let rec subset_size (#a:eqtype) #f x y = match x, y with
  | [], _          -> ()
  | hd::tl, hd'::(tl':ordset a f) ->
    if f hd hd' && hd = hd' then subset_size tl tl'
    else subset_size x tl'
  
let insert_when_already_exists (#a:eqtype) #f (s: ordset a f) (x:a)
  : Lemma (requires mem x s) 
          (ensures insert' x s == s)  
  = simple_induction (fun p -> mem x p <==> insert' x p = p) s
  
let size_insert (#a:eqtype) #f (s: ordset a f) (x:a)
  : Lemma (size (insert' x s) >= size s) 
  = simple_induction (fun p -> size (insert' x p) >= size p) s
  
let rec precise_size_insert (#a:eqtype) #f (s: ordset a f) (x:a)
  : Lemma (size (insert' x s) = (if mem x s then size s else (size s) + 1)) 
  = if size s > 0 then precise_size_insert (tail s) x
       
let rec size_of_union_left (#a:eqtype) #f (s1 s2: ordset a f)
  : Lemma (ensures size (union s1 s2) >= size s2) = 
  match s1 with
  | [] -> ()
  | hd::tl -> size_of_union_left tl (insert' hd s2);
            precise_size_insert s2 hd

let size_of_union_right (#a:eqtype) #f (s1 s2: ordset a f)
  : Lemma (ensures size (union s1 s2) >= size s1) =
  eq_lemma (union s1 s2) (union s2 s1);
  size_of_union_left s2 s1

let size_union #a #f s1 s2 =
  size_of_union_left s1 s2;
  size_of_union_right s1 s2
 
let fold #a #acc #f g init s = List.Tot.fold_left g init s

private
let rec map_internal (#a #b:eqtype) (#fa:cmp a) (#fb:cmp b) (g:a -> b) (sa:ordset a fa)
  : Pure (ordset b fb)
    (requires (forall x y. (x `fa` y ==> g x `fb` g y) /\ (x = y <==> g x = g y)))
    (ensures (fun sb -> Cons? sb ==> Cons? sa /\ Cons?.hd sb == g (Cons?.hd sa)))
= match sa with
  | [] -> []
  | x :: xs ->
    let y = g x in
    let ys = map_internal #a #b #fa #fb g xs in
    if not (Cons? ys) || Cons?.hd ys <> y then
      y :: ys
    else ys

let rec map_size (#a #b:eqtype) (#fa:cmp a) (#fb: cmp b) (g: a->b) (sa:ordset a fa)
  : Lemma (requires (forall x y. (x `fa` y ==> g x `fb` g y) /\ (x = y <==> g x = g y)))
          (ensures size (map_internal #a #b #fa #fb g sa) <= size sa) 
  = if size sa > 0 then map_size #a #b #fa #fb g (tail sa)

let rec map_as_list (#a #b:eqtype) (#fa:cmp a) (#fb: cmp b) (g: a->b) (sa:ordset a fa)
  : Lemma (requires (forall x y. (x `fa` y ==> g x `fb` g y) /\ (x = y <==> g x = g y)))
          (ensures as_list (map_internal #a #b #fa #fb g sa) == FStar.List.Tot.map g (as_list sa)) = 
  match sa with
  | [] -> ()
  | h::(t:ordset a fa) -> map_as_list #a #b #fa #fb g t 

let map #a #b #fa #fb g sa = 
  map_size #a #b #fa #fb g sa;
  map_as_list #a #b #fa #fb g sa;
  map_internal #a #b #fa #fb g sa

let lemma_strict_subset_size #a #f s1 s2 = 
  let eql (p q: ordset a f) 
    : Lemma (requires forall x. mem x p = mem x q) 
            (ensures p=q) 
    = eq_lemma p q in Classical.move_requires_2 eql s1 s2;
  eliminate exists x. mem x s2 && not (mem x s1) 
  returns size s2 > size s1 with _.
  begin
    Classical.forall_intro (mem_insert x s1);
    precise_size_insert s1 x;
    assert (subset (insert' x s1) s2)
  end
   
let lemma_minus_mem #a #f s1 s2 x = ()
 
let rec strict_subset_implies_diff_element #a #f (s1 s2: ordset a f) 
  : Lemma (requires strict_subset s1 s2)
          (ensures exists x. (mem x s2 /\ not (mem x s1))) = 
  match s1,s2 with
  | [], h::t -> ()
  | h1::t1, h2::t2 -> Classical.move_requires (mem_implies_f s1) h2;
                   if h1=h2 then begin
                     strict_subset_implies_diff_element #a #f t1 t2; 
                     set_props s2                     
                   end

let diff_element_implies_strict_subset #a #f (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2 /\ (exists x. (mem x s2 /\ not (mem x s1))))
          (ensures strict_subset s1 s2) = ()

let lemma_strict_subset_exists_diff #a #f (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2)
          (ensures (strict_subset s1 s2) <==> (exists x. (mem x s2 /\ not (mem x s1)))) 
  = Classical.move_requires_2 strict_subset_implies_diff_element s1 s2
 
let rec count #a #f s c : nat = 
  match s with
  | [] -> 0
  | h::t -> if c h 
          then 1 + count #a #f t c 
          else count #a #f t c

let count_of_empty #_ #_ _ _ = ()

let count_of_impossible #a #f s c = simple_induction (fun p -> count p c = 0) s

let count_all #a #f s c = simple_induction (fun p -> count p c = size p) s

let rec count_of_cons #a #f s c = if size s > 1 then count_of_cons (tail s) c 

let rec all #a #f (s: ordset a f) (c: condition a) : Tot bool = 
  match s with
  | [] -> true
  | h::t -> c h && all #a #f t c

let rec any #a #f (s: ordset a f) (c: condition a) : Tot bool = 
  match s with
  | [] -> false
  | h::t -> c h || any #a #f t c

let rec mem_if_any #a #f s c x = if head s<>x then mem_if_any (tail s) c x

let any_if_mem #a #f (s:ordset a f) (c: condition a) x
  : Lemma (requires mem x s && c x) (ensures any s c) = 
  simple_induction (fun p -> mem x p && c x ==> any p c) s
 
let all_means_not_any_not #a #f s c = simple_induction (fun p -> all p c = not (any p (inv c))) s

let rec find_first #a #f s c = match s with
  | [] -> None
  | h::(t:ordset a f) -> if c h then Some h else find_first t c

let find_first_is_some_iff_any #_ #_ s c = simple_induction (fun p -> Some? (find_first p c) = any p c) s
 
let rec find_first_precedes_any_other #a #f s c x =   
  if head s<>x then find_first_precedes_any_other (tail s) c x;
  set_props s

let liat_size #a #f (s:ordset a f{s<>[]}) : Lemma (size (liat s) = size s - 1) = 
  base_induction (fun p -> if p<>[] then size (liat p) = size p - 1 else true) s

let mem_liat #a #f (s:ordset a f{s<>[]}) (x:a)
  : Lemma (mem x s = (mem x (liat s) || x = last s)) = ()

let rec any_liat #a #f (s:ordset a f{s<>[]}) (c: condition a)
  : Lemma (any s c = (any (liat s) c || c (last s))) = match s with
  | [x] -> ()
  | h::(t:ordset a f) -> if size t > 0 then any_liat t c

let rec find_last' #a #f (s: ordset a f) (c: condition a) : Tot (option a) (decreases size s) =
  if s=empty then None 
  else let liat,last = unsnoc s in
    liat_size s;
    if c last then Some last
    else find_last' liat c

let rec find_last_props #a #f (s:ordset a f) (c: condition a)
  : Lemma (ensures (match find_last' s c with
           | None -> not (any s c)
           | Some v -> (any s c /\ (forall (x:a{mem x s && c x}). f x v))))
          (decreases size s) =
  if size s > 0 then let liat,last = unsnoc s in
    liat_size s;     
    find_last_props liat c; 
    if c last then any_if_mem s c last else any_liat s c  

let find_last #a #f s c = 
  find_last_props s c;
  find_last' s c

let find_last_is_some_iff_any #a #f s c = find_last_props s c

let find_last_follows_any_other #a #f s c x = 
  any_if_mem s c x; 
  find_last_is_some_iff_any s c;
  find_last_props s c
  
let size_of_tail #a #f s  = ()
 
let count_of_tail #_ #_ _ _ = () 

let rec where #a #f s c = 
  match s with
  | [] -> []
  | h::[] -> if c h then [h] else []
  | h::(t:ordset a f) -> if c h then h::(where t c) else where t c 
 
let intersect_eq_where #_ #_ s1 s2 = 
  same_members_means_eq (where s1 (mem_of s2)) (intersect s1 s2)

let minus_eq_where #_ #_ s1 s2 = 
  same_members_means_eq (where s1 (inv (mem_of s2))) (minus s1 s2)

let count_is_size_of_where #_ #_ s c 
  = simple_induction (fun p -> count p c = size (where p c)) s

let size_of_intersect #_ #_ s1 s2 =    
  intersect_eq_where s1 s2;
  intersect_eq_where s2 s1;
  intersect_is_symmetric s1 s2;
  count_is_size_of_where s1 (mem_of s2);   
  count_is_size_of_where s2 (mem_of s1)
    
let union_mem_forall #a #f (s1 s2: ordset a f)
  : Lemma (forall x. (mem x (union s1 s2)) = (mem x s1 || mem x s2)) =
  let aux x : Lemma (mem x (union s1 s2) = (mem x s1 || mem x s2)) =   
    mem_union s1 s2 x in Classical.forall_intro aux  

let union_with_empty #a #f (s: ordset a f) 
  : Lemma (union s empty = s) = eq_lemma (union s empty) s

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

let union_is_symmetric #a #f (s1 s2: ordset a f) : Lemma (union s1 s2 = union s2 s1) = 
  same_members_means_eq (union s1 s2) (union s2 s1)
 
let size_of_union_aux_1 #a #f (s1 s2: (z:ordset a f{z<>empty}))
  : Lemma (requires (head s1) <> (head s2) 
                 && (f (head s1) (head s2)) 
                 && (size (union (tail s1) s2) = size (tail s1) + size s2 - size (intersect (tail s1) s2)))
          (ensures size (union s1 s2) = (size s1 + size s2 - size (intersect s1 s2))) =  
    union_of_tails_size s1 s2;
    same_members_means_eq (intersect (tail s1) s2) (intersect s1 s2)

let size_of_union_aux_2 #a #f (s1 s2: (z:ordset a f{z<>empty}))
  : Lemma (requires (head s1) <> (head s2) 
                 && not (f (head s1) (head s2)) 
                 && (size (union s1 (tail s2)) = size s1 + size (tail s2) - size (intersect s1 (tail s2))))
          (ensures size (union s1 s2) = (size s1 + size s2 - size (intersect s1 s2))) 
  = Classical.forall_intro_2 (union_is_symmetric #a #f);
    Classical.forall_intro_2 (intersect_is_symmetric #a #f);
    size_of_union_aux_1 s2 s1 
     
let rec size_of_union #a #f s1 s2 = 
  let size = size #a #f in
  match s1,s2 with
  | [], _ -> same_members_means_eq s2 (union s1 s2)
  | _, [] -> same_members_means_eq s1 (union s1 s2)
  | h1::(t1:ordset a f), h2::(t2:ordset a f) 
          -> size_of_union t1 s2;
            size_of_union s1 t2;
            if h1 = h2 then union_with_prefix h1 t1 t2
            else if f h1 h2 then size_of_union_aux_1 s1 s2 
            else size_of_union_aux_2 s1 s2   

let rec count_dichotomy #_ #_ s c = if s<>[] then count_dichotomy (tail s) c

let size_of_minus #_ #_ s1 s2 =
  minus_eq_where s1 s2;
  intersect_eq_where s1 s2; 
  count_dichotomy s1 (mem_of s2); 
  count_is_size_of_where s1 (mem_of s2);
  count_is_size_of_where s1 (inv (mem_of s2))
 
let intersect_with_subset #_ #_ s1 s2 = same_members_means_eq (intersect s1 s2) s1
 
let lemma_strict_subset_minus_size #_ #_ s1 s2 s = 
  let size_diff : pos = size s2 - size s1 in
  size_of_minus s s2;
  size_of_minus s s1;
  intersect_with_subset s2 s;
  intersect_is_symmetric s2 s;
  intersect_with_subset s1 s;
  intersect_is_symmetric s1 s

let lemma_disjoint_union_subset #_ #_ s1 s2 = size_of_union s1 s2

let lemma_subset_union #_ #_ _ _ _ = ()

let lemma_strict_subset_transitive #_ #_ _ _ _ = ()

let lemma_intersect_symmetric = intersect_is_symmetric

let lemma_intersect_union_empty_aux1 #a #f (s1 s2 s3: ordset a f) 
  : Lemma (requires (intersect s1 s3 == empty /\ intersect s2 s3 == empty))
          (ensures (intersect (union s1 s2) s3 = empty))
  = eq_lemma empty (intersect (union s1 s2) s3)

let lemma_intersect_union_empty_aux2 #a #f (s1 s2 s3: ordset a f)  
  : Lemma (requires (intersect (union s1 s2) s3 = empty))
          (ensures (intersect s1 s3 == empty /\ intersect s2 s3 == empty))  
  = eq_lemma empty (intersect s1 s3);
    eq_lemma empty (intersect s2 s3) 

let lemma_intersect_union_empty #a #f (s1 s2 s3: ordset a f)
  : Lemma ((intersect (union s1 s2) s3 = empty) = 
           (intersect s1 s3 = empty && intersect s2 s3 = empty))
    [SMTPat (intersect (union s1 s2) s3)] =  
  Classical.move_requires_3 (lemma_intersect_union_empty_aux1 #a #f) s1 s2 s3;
  Classical.move_requires_3 (lemma_intersect_union_empty_aux2 #a #f) s1 s2 s3

let lemma_union_symmetric #a #f s1 s2 = eq_lemma (union s1 s2) (union s2 s1)

let union_of_disjoint #a #f s1 s2 = eq_lemma (minus (union s1 s2) s1) s2

let distinct_is_idempotent #a #f s = eq_lemma (distinct f s) s

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

let lemma_as_set_disjoint_right #a #f (s1 s2: ordset a f)
  : Lemma (requires intersect s1 s2 = empty)
          (ensures S.disjoint (as_set s1) (as_set s2)) = ()

let lemma_as_set_disjoint_left #a #f (s1 s2: ordset a f)
  : Lemma (requires S.disjoint (as_set s1) (as_set s2)) 
          (ensures intersect s1 s2 = empty) =     
  let mem_eq p q : Lemma (S.mem p (as_set q) <==> mem #a #f p q) = () in
  Classical.forall_intro_2 mem_eq

let lemma_as_set_disjoint #a #f s1 s2 = 
  Classical.move_requires_2 (lemma_as_set_disjoint_right #a #f) s1 s2;
  Classical.move_requires_2 (lemma_as_set_disjoint_left #a #f) s1 s2
