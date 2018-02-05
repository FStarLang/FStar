(*
  Defines the origin of a uri (scheme, domain, port)
*)
module Web.Origin

open AuxiliaryFunctions

module List = FStar.List.Tot

#reset-options "--z3rlimit 100"

type origin_protocol = s:string{s="" || s="http" || s="https" || s="javascript" || s="ftp" || s="ws" || s="data"}
type origin_domain = list string
type origin_port = int

(* protocol://host:origin_port e.g. https://cnn.com:443 *)
(* 
   OpaqueOrigin -> opaque domain a unique domain for every opaque domain - also used to assign browser ids
   OriginStar is used mostly for cookies to indicate that any of the domain's subdomain can access it 
*)
type origin = 
| Origin : protocol:origin_protocol -> host:origin_domain -> port:option origin_port -> dom:option origin_domain -> origin
| OpaqueOrigin : unique_id:nat -> origin

type origin_tuple = o:origin{Origin? o}
type origin_opaque = o:origin{OpaqueOrigin? o}

let blank_origin = (Origin "" [] None None)

val is_origin_protocol : string -> Tot bool
let is_origin_protocol s = (s="" || s="http" || s="https" || s="javascript" || s="ftp" || s="ws" || s="data")

val origin_domain_to_string : list string -> Tot string
let rec origin_domain_to_string hd = 
  match hd with 
  | [] -> ""
  | h::t -> h ^ (if t = [] then "" else "." ^ (origin_domain_to_string t))

val origin_to_string : origin -> Tot string
let origin_to_string o = 
    match o with 
    | OpaqueOrigin _ -> "Opaque"
    | Origin s h p d -> (s ^ "://" ^ (origin_domain_to_string h) ^ (if p <> None then ":" ^ string_of_int (Some?.v p) else ""))  

(* bad origin_port - 3.5 Fetch spec *)
val port_is_bad : origin_port -> Tot bool
let port_is_bad p = (p=1 || p=7 || p=9 || p=11 || p=13 || p=15 || p=17 || p=19 || p=20 || p=21 || p=22 || p=23 || p=25 || p=37 || p=42 || p=43 || p=53 || p=77 || p=79 || p=87 || p=95 || p=101 || p=102 || p=103 || p=104 || p=109 || p=110 || p=111 || p=113 || p=115 || p=117 || p=119 || p=123 || p=135 || p=139 || p=143 || p=179 || p=389 || p=465 || p=512 || p=513 || p=514 || p=515 || p=526 || p=530 || p=531 || p=532 || p=540 || p=556 || p=563 || p=587 || p=601 || p=636 || p=993 || p=995 || p=2049 || p=3659 || p=4045 || p=6000 || p=6665 || p=6666 || p=6667 || p=6668 || p=6669)

(* Section 7.5 HTML 5.1 sameorigin *)
val is_same_origin : o0:origin -> o1:origin -> Tot bool
let is_same_origin o0 o1 = 
  match o0 with 
  | OpaqueOrigin n -> if (o1 = OpaqueOrigin n) then true else false
  | Origin s0 h0 p0 _ -> (match o1 with 
	      | Origin s1 h1 p1 _ -> (s0 = s1 && h0 = h1 && p0 = p1)
	      | _ -> false) 

(* Section 7.5 HTML 5.1 sameorigindomain *)
val is_same_origin_domain : o0:origin -> o1:origin -> Tot bool
let is_same_origin_domain o0 o1 = 
  (o0 = o1) || 
  (match o0 with 
  | OpaqueOrigin n -> if (o1 = OpaqueOrigin n) then true else false
  | Origin s0 h0 p0 d0 -> match o1 with 
	      | OpaqueOrigin _ -> false
	      | Origin s1 h1 p1 d1 -> 
		  if (s0 = s1 && d0 = d1 && d0 <> None) then true
		  else if ((is_same_origin o0 o1) && d0 = None && d1 = None) then true
		  else false)

(* is Same origin in the list of origins *)
val is_same_origin_in_list_sub : origin_tuple -> list origin_tuple -> Tot bool
let rec is_same_origin_in_list_sub o l = (List.mem o l) ||
  (match l with
  | [] -> false
  | hd::tl -> (is_same_origin_domain o hd) || (is_same_origin_in_list_sub o tl))

(* is Same origin in the list of origins *)
val is_same_origin_in_list : list origin_tuple -> list origin_tuple -> Tot bool
let rec is_same_origin_in_list l l' =
  match l with
  | [] -> false
  | hd::tl -> (is_same_origin_in_list_sub hd l') || (is_same_origin_in_list tl l')

(* Check if list in l is a sub-sequence of list in l' *)
val origin_domain_match_sub : l:list string -> l':list string -> Tot (b:bool{b ==> (forall x. List.mem x l ==> (x = "*" \/ List.mem x l'))})
let rec origin_domain_match_sub l l' =
  match l with
  | [] -> true
  | hd::tl -> if hd = "*" && tl = [] then true
	    else 
	      match l' with
	      | [] -> false
	      | hd'::tl' -> if hd = hd' then origin_domain_match_sub tl tl'
			 else false

(* As origin_domain is a list of strings where each string contains of only characters without periods, 
   it suffices to check if the complete second list is present in the first list. 
   For a reversed list, the second list is prefix of the first list
   -- d domain-matches d' 
*)
(* Is the origin "d" a subdomain of "d'", i.e., is "d'" a suffix of "d" *)
val origin_domain_match : d:origin_domain -> d':origin_domain -> Tot (b:bool{b ==> (forall x. List.mem x (list_reverse d') ==> (x = "*" \/ List.mem x (list_reverse d)))})
let origin_domain_match d d' = 
  (let rd = list_reverse d in
  let rd' = list_reverse d' in 
  origin_domain_match_sub rd' rd)

(* Match an origin domain with list of domains *)
val is_origin_domain_in_list : origin_domain -> list origin_domain -> Tot bool
let rec is_origin_domain_in_list h l =
  match l with
  | [] -> false
  | hd::tl -> if (origin_domain_match h hd) then true
	    else is_origin_domain_in_list h tl 

(* Match an origin with a domain *)
val is_origin_match_origin_domain : origin -> origin_domain -> Tot bool
let is_origin_match_origin_domain o d =
  match o with
  | OpaqueOrigin _ -> false
  | Origin _ host _ _ -> origin_domain_match host d (* host is of the format "a.b.c" and d is of the format "*.b.c" *)

(* check if the list of origins l is a sublist of list of origins s *)
val origin_list_is_sublist : l:list origin -> s:list origin -> Tot (b:bool{b ==> (forall o. List.mem o l ==> List.mem o s)}) 
let rec origin_list_is_sublist l s = 
  (match l with 
  | [] -> true
  | hd::tl -> (List.mem hd s) && (origin_list_is_sublist tl s))

val origin_list_append_member_lemma : l_1:list origin -> l_2:list origin -> 
			       Lemma (requires True) (ensures ((forall x. List.mem x l_1 ==> List.mem x (List.append l_1 l_2)) /\ 
						    (forall x. List.mem x l_2 ==> List.mem x (List.append l_1 l_2)))) 
			       [SMTPat (List.append l_1 l_2)]
let rec origin_list_append_member_lemma l l' = 
  match l with 
  | [] -> ()
  | hd::tl -> origin_list_append_member_lemma tl l'

val origin_list_append_member_sublist_lemma : l_1:list origin -> l_2:list origin -> 
			       Lemma (requires (forall x. List.mem x l_1 ==> List.mem x l_2)) (ensures (origin_list_is_sublist l_1 l_2)) 
			       [SMTPat (origin_list_is_sublist l_1 l_2)]
let rec origin_list_append_member_sublist_lemma l l' =  
  match l with 
  | [] -> ()
  | hd::tl -> origin_list_append_member_sublist_lemma tl l'

val origin_list_append_sublist_lemma : l_1:list origin -> l_2:list origin ->
			Lemma (requires True) (ensures (origin_list_is_sublist l_1 (List.append l_1 l_2))) 
			[SMTPat (List.append l_1 l_2)]
let rec origin_list_append_sublist_lemma l l' = 
  match l with 
  | [] -> ()
  | hd::tl -> origin_list_append_sublist_lemma tl l'


 

(* for printing and logging *)
val origin_list_to_string : list origin -> Tot (string)
let rec origin_list_to_string l =
  match l with 
  | [] -> ""
  | hd::tl -> "Origin: " ^ (origin_to_string hd) ^ "\n" ^ (origin_list_to_string tl)

(* (\* match origin-domain of a proper tuple origin with origin* in the list of origin for domain match *\) *)
(* val is_origin_domain_match_star : origin_domain -> origin -> Tot bool *)
(* let is_origin_domain_match_star h o =  *)
(*     match o with  *)
(*     | OriginStar host -> origin_domain_match h host *)
(*     | _ -> false *)

(* val is_origin_match_origin : origin -> origin -> Tot bool *)
(* let is_origin_match_origin h lo =  *)
(*     match lo with  *)
(*     | OriginStar host -> is_origin_domain_match_origin host h *)
(*     | _ -> h = lo *)


(* val origin_list_sublist_lemma : ol:list origin -> ol':list origin ->  *)
(* 				Lemma (requires (origin_list_is_sublist ol ol'))  *)
(* 				(ensures (forall x. is_origin_in_list_origins x ol ==> is_origin_in_list_origins x ol')) *)
(* let rec origin_list_sublist_lemma ol ol' =  *)
(*   match ol with  *)
(*   | [] -> () *)
(*   | hd::tl -> origin_list_sublist_lemma tl ol' *)
