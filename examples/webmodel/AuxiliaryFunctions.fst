(*
  Contains some auxiliary functions related to lists and 
  definition of the dictionary data structure
*)

module AuxiliaryFunctions

module List = FStar.List.Tot

(* AUXILIARY FUNCTIONS *)
(* Takes a counter n initialized to 0 *)
val pos : #a:eqtype -> a -> l:(list a) -> n:nat -> Tot nat
let rec pos #a e l n =
  match l with 
  | [] -> 0
  | hd::tl -> if hd=e then n+1
	    else pos e tl n+1

val eqIndex : #a:eqtype -> l:(list a) -> n:nat{n > 0 && n <= List.length l} -> Tot (e:a{List.mem e l})
let rec eqIndex #a l n =
  if n = 1 then
    List.hd l
  else
    eqIndex (List.tl l) (n - 1)
    
(* Replace an element in the list *)
val replace_elem_list : #a:eqtype -> l:list a -> n:nat -> e:a -> Tot (nl:(list a){List.length l = List.length nl})
let rec replace_elem_list #a l n e =
  if (n = 0) then l
  else if (n > List.length l) then l
  else if (n = 1) then (match l with 
		       | hd::tl -> e::tl)
  else (match l with
	| hd::tl -> hd::(replace_elem_list tl (n-1) e))

val replace_lemma : #a:eqtype -> l:list a -> n:nat -> e:a -> 
		  Lemma (requires True) (ensures (forall x. List.mem x (replace_elem_list l n e) ==> (List.mem x l) \/ (x=e))) [SMTPat (replace_elem_list l n e)]
let rec replace_lemma #a l n e = 
  if (n = 0) then ()
  else if (n > List.length l) then ()
  else if (n = 1) then ()
  else match l with |_::tl -> replace_lemma tl (n-1) e 
  
(* Remove an element in the list *)
val remove_elem_list_n : l:list 'a -> n:nat{n <= List.length l} -> Tot (list 'a)
let rec remove_elem_list_n l n =
  if (n = 0) then l
  else if (n = 1) then (match l with 
		       | hd::tl -> tl)
  else (match l with
	| hd::tl -> hd::(remove_elem_list_n tl (n-1)))

val remove_elem_list : #a:eqtype -> list a -> a -> Tot (list a)
let rec remove_elem_list #a lc c =
  match lc with
  | [] -> []
  | hd::tl -> if hd=c then tl
	    else remove_elem_list tl c

val removeDuplicates : #a:eqtype -> list a -> Tot (list a)
let rec removeDuplicates #a l =
  match l with
  | [] -> []
  | hd::tl -> if (not(List.mem hd tl)) then hd::(removeDuplicates tl)
	    else (removeDuplicates tl)

(* Is "l" a sublist of "s", i.e., all elements of "l" are present in "s" *)
(* No implementation for subset function in List.Tot.Base *)
val isSublist : #a:eqtype -> l:list a -> s:list a -> Tot (bool)
let rec isSublist #a l s =
  match l with 
  | [] -> true
  | hd::tl -> (List.mem hd s) && (isSublist tl s)
	    
val emptyList : l: list 'a -> Tot bool
let emptyList l = 
  match l with | [] -> true | _ -> false

val firstElement : l:(list 'a){not (emptyList l)} -> Tot 'a
let firstElement l =
  match l with
  | hd::_ -> hd

(* checks if the length of the list is less than or equal to 1. check if header values are at most 1 *)
val singleValue : list 'a -> Tot bool
let singleValue ls = (List.length ls = 1)

val list_to_string : l:list string -> Tot string
let rec list_to_string l =
  match l with
  | [] -> ""
  | h::t -> h ^ (list_to_string t)

(* Remove entries after the nth entry *)
val rem_sublist : #a:eqtype -> l:list a -> n:nat -> Tot (fl:(list a){(if n <= List.length l then List.length fl = n else List.length l = List.length fl) /\ List.length fl <= n})
let rec rem_sublist #a l n =
    if n = 0 then []
    else (match l with
	 | [] -> []
	 | h::t -> h::(rem_sublist t (n-1)))

val sublist_lemma : #a:eqtype -> l:list a -> n:nat -> 
		  Lemma (requires True) (ensures (forall x. List.mem x (rem_sublist l n) ==> List.mem x l))
		      [SMTPat (rem_sublist #a l n)]
let rec sublist_lemma #a l n = 
  if n = 0 then ()
  else match l with | [] -> () | h::tl -> sublist_lemma tl (n-1)

val lemma_list_append : l:list 'a -> l':list 'a -> 
			Lemma (requires True) (ensures (List.length (List.append l l') = (List.length l + List.length l'))) [SMTPat (List.append l l')]
let rec lemma_list_append l l' = 
  match l with 
  | [] -> ()
  | hd::tl -> lemma_list_append tl l'

(* Dictionary *)
type kvpair = {key:string; value:string}
type dictionary = list kvpair

(* Dictionary functions *)
val get_val_dict : dictionary -> string -> Tot string
let get_val_dict d k =
  let mem = List.find (fun kv -> kv.key = k) d in
  match mem with
  | None -> ""
  | Some kv -> kv.value

(* Remove the key-value pair from the dictionary and return a new dictionary*)
val remove_kv_dict : dictionary -> string -> Tot dictionary
let rec remove_kv_dict d k =
  match d with
  | [] -> []
  | h::t -> if h.key = k then t
	  else h::(remove_kv_dict t k) 

(* Set the value of the key in the given dictionary *)
(* The order of the properties is not preserved here. This might not be important as the key is always unique for a given store *)
val set_val_dict : dictionary -> string -> string -> Tot dictionary
let set_val_dict d k v =
  let kvp = {key=k;value=v} in 
  let mem = List.find (fun kv -> kv.key = k) d in
  match mem with
  | None -> kvp::d
  | Some kv -> let nd = remove_kv_dict d kv.key in
      kvp::nd

