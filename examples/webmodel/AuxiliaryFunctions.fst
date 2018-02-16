(*
  Contains some auxiliary functions related to lists and 
  definition of the dictio.ary data structure
*)

module AuxiliaryFunctions

module List = FStar.List.Tot

(* AUXILIARY FUNCTIONS *)
(* Takes a counter n initialized to 0 *)
val list_element_position : #a:eqtype -> a -> l:(list a) -> n:nat -> Tot nat
let rec list_element_position #a e l n =
  match l with 
  | [] -> 0
  | hd::tl -> if hd=e then n+1
	    else list_element_position e tl n+1

val list_element_at : #a:eqtype -> l:(list a) -> n:nat{n > 0 && n <= List.length l} -> Tot (e:a{List.mem e l})
let rec list_element_at #a l n =
  if n = 1 then
    List.hd l
  else
    list_element_at (List.tl l) (n - 1)
    
(* Replace an element in the list *)
val list_replace_element_at : #a:eqtype -> l:list a -> n:nat -> e:a -> Tot (nl:(list a){List.length l = List.length nl})
let rec list_replace_element_at #a l n e =
  if (n = 0) then l
  else if (n > List.length l) then l
  else if (n = 1) then (match l with 
		       | hd::tl -> e::tl)
  else (match l with
	| hd::tl -> hd::(list_replace_element_at tl (n-1) e))

val list_replace_lemma : #a:eqtype -> l:list a -> n:nat -> e:a -> 
		  Lemma (requires True) (ensures (forall x. List.mem x (list_replace_element_at l n e) ==> (List.mem x l) \/ (x=e))) [SMTPat (list_replace_element_at l n e)]
let rec list_replace_lemma #a l n e = 
  if (n = 0) then ()
  else if (n > List.length l) then ()
  else if (n = 1) then ()
  else match l with |_::tl -> list_replace_lemma tl (n-1) e 
  
(* Remove an element in the list *)
val list_remove_element_at : l:list 'a -> n:nat{n <= List.length l} -> Tot (list 'a)
let rec list_remove_element_at l n =
  if (n = 0) then l
  else if (n = 1) then (match l with 
		       | hd::tl -> tl)
  else (match l with
	| hd::tl -> hd::(list_remove_element_at tl (n-1)))

val list_remove_element : #a:eqtype -> list a -> a -> Tot (list a)
let rec list_remove_element #a l e =
  match l with
  | [] -> []
  | hd::tl -> if hd=e then tl
	    else hd::(list_remove_element tl e)

val list_remove_duplicates : #a:eqtype -> list a -> Tot (list a)
let rec list_remove_duplicates #a l =
  match l with
  | [] -> []
  | hd::tl -> if (not (List.mem hd tl)) then hd::(list_remove_duplicates tl)
	    else (list_remove_duplicates tl)

(* Is "l" a sublist of "s", i.e., all elements of "l" are present in "s" *)
(* No implementation for subset function in List.Tot.Base --- the current implementation doesn't account for duplicates separately *)
val list_is_sublist : #a:eqtype -> l:list a -> s:list a{List.length s >= List.length l} -> Tot (b:bool{b ==> (forall x. List.mem x l ==> List.mem x s)})
let rec list_is_sublist #a l s = 
  (match l with 
  | [] -> true
  | hd::tl -> (List.mem hd s) && (list_is_sublist tl s))

val list_is_empty : l: list 'a -> Tot bool
let list_is_empty l = match l with | [] -> true | _ -> false

(* checks if the length of the list is less than or is_equal_secret_string to 1. check if header values are at most 1 *)
val list_is_single_element_list : list 'a -> Tot bool
let list_is_single_element_list ls = (List.length ls = 1)

val list_to_string : l:list string -> Tot string
let rec list_to_string l =
  match l with
  | [] -> ""
  | h::t -> h ^ (list_to_string t)

(* Similar to a set-difference operation *)
val list_difference : #t:eqtype -> a:list t -> b:list t -> Tot (c:(list t){forall x. List.mem x b ==> not (List.mem x c)})
let rec list_difference #t a b =
  match a with 
  | [] -> []
  | h::t -> if (List.mem h b) then list_difference t b else h::(list_difference t b)

(* Remove entries after the nth entry *)
val list_remove_sublist : #a:eqtype -> l:list a -> n:nat -> 
			  Tot (fl:(list a){(if n <= List.length l then List.length fl = n else List.length l = List.length fl) /\ List.length fl <= n})
let rec list_remove_sublist #a l n =
    if n = 0 then []
    else (match l with
	 | [] -> []
	 | h::t -> h::(list_remove_sublist t (n-1)))

val rem_list_sublist_lemma : #a:eqtype -> l:list a -> n:nat -> 
		  Lemma (requires True) (ensures (forall x. List.mem x (list_remove_sublist l n) ==> List.mem x l))
		      [SMTPat (list_remove_sublist #a l n)]
let rec rem_list_sublist_lemma #a l n = 
  if n = 0 then ()
  else match l with | [] -> () | h::tl -> rem_list_sublist_lemma tl (n-1)

val list_append_lemma : l:list 'a -> l':list 'a -> 
			Lemma (requires True) (ensures (List.length (List.append l l') = (List.length l + List.length l'))) [SMTPat (List.append l l')]
let rec list_append_lemma l l' = 
  match l with 
  | [] -> ()
  | hd::tl -> list_append_lemma tl l'

val list_append_member_lemma : #a:eqtype -> l_1:list a -> l_2:list a -> 
			       Lemma (requires True) (ensures ((forall x. List.mem x l_1 ==> List.mem x (List.append l_1 l_2)) /\ 
						    (forall x. List.mem x l_2 ==> List.mem x (List.append l_1 l_2)))) 
			       [SMTPat (List.append l_1 l_2)]
let rec list_append_member_lemma #a l l' = 
  match l with 
  | [] -> ()
  | hd::tl -> list_append_member_lemma tl l'

val list_append_member_sublist_lemma : #a:eqtype -> l_1:list a -> l_2:list a{List.length l_2 >= List.length l_1} -> 
			       Lemma (requires (forall x. List.mem x l_1 ==> List.mem x l_2)) (ensures (list_is_sublist l_1 l_2)) 
			       [SMTPat (list_is_sublist l_1 l_2)]
let rec list_append_member_sublist_lemma #a l l' =  
  match l with 
  | [] -> ()
  | hd::tl -> list_append_member_sublist_lemma tl l'

val list_append_sublist_lemma : #a:eqtype -> l_1:list a -> l_2:list a{List.length l_2 >= List.length l_1} ->
			Lemma (requires True) (ensures (list_is_sublist l_1 (List.append l_1 l_2) /\ list_is_sublist l_2 (List.append l_1 l_2))) [SMTPat (List.append l_1 l_2)]
let rec list_append_sublist_lemma #a l l' = 
  match l with 
  | [] -> ()
  | hd::tl -> list_append_sublist_lemma tl l'

(* reverse a list *)
val list_reverse : #a:eqtype -> l:list a -> Tot (fl:list a{List.length l = List.length fl /\ (forall x. List.mem x l ==> List.mem x fl)})
let rec list_reverse #a l = match l with
    | [] -> []
    | hd::tl -> list_append_member_lemma (list_reverse tl) [hd]; 
	      list_append_lemma (list_reverse tl) [hd]; 
	      List.append (list_reverse tl) [hd]




(* Dictionary *)
type key_value_pair (#a:eqtype) (#b:eqtype) = {key:a; value:b}
type dictionary (#a:eqtype) (#b:eqtype) = list (key_value_pair #a #b)

(* Dictionary functions *)
val dictionary_get_value : #a:eqtype -> #b:eqtype -> dictionary #a #b -> a -> Tot (option b)
let dictionary_get_value #a #b d k =
  match List.find (fun kv -> kv.key = k) d with
  | None -> None
  | Some kv -> Some (kv.value)

(* Remove the key-value pair from the dictionary and return a new dictionary*)
val dictionary_remove_pair : #a:eqtype -> #b:eqtype -> dictionary #a #b -> a -> Tot (dictionary #a #b)
let rec dictionary_remove_pair #a #b d k =
  match d with
  | [] -> []
  | h::t -> if h.key = k then t
	  else h::(dictionary_remove_pair t k) 

(* Set the value of the key in the given dictionary *)
(* The order of the properties is not preserved here. This might not be important as the key is always unique for a given store *)
val dictionary_set_value : #a:eqtype -> #b:eqtype -> dictionary #a #b -> a -> b -> Tot (dictionary #a #b)
let dictionary_set_value #a #b d k v =
  let kvp = {key=k;value=v} in 
  let mem = List.find (fun kv -> kv.key = k) d in
  match mem with
  | None -> kvp::d
  | Some kv -> let nd = dictionary_remove_pair d kv.key in
      kvp::nd

