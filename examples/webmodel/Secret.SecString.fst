(*
  Module to define the structure of a secret string. 
  A string can either be public or secret indexed by origins
  It also defines the different functions for handling the secrets
*)
module Secret.SecString

open FStar.String
open Web.Origin
open ML.ExternalFunctions
open AuxiliaryFunctions

module List = FStar.List.Tot

(* Secrecy origins are the indices to secrets - can either be an origin or a origin* with wildcard checks, e.g., cookies *)
type secrecy_origin = 
| SecOrigin : orig:origin -> secrecy_origin
| OriginStar : host:origin_domain -> secrecy_origin

type secrecy_origin_list = lo:list secrecy_origin{not (list_is_empty lo)}
type origin_star = o:secrecy_origin{OriginStar? o}

(* Secrecy level *)
type secrecy_level = 
| PublicVal : secrecy_level
| SecretVal : sec_origin_list:secrecy_origin_list -> secrecy_level

(* abstract *) 
type a_string (ol:secrecy_origin_list) = 
     | AString : string -> a_string ol

let secret_string (s:secrecy_level): Tot Type0 =
     match s with
     | PublicVal -> string
     | SecretVal ol -> a_string ol

type public_string = secret_string PublicVal

(* all secrets with possible list of origins for a particular user -- "&" represents dependent type *)
type global_secrets_list_origins = list (secret_value:(l:secrecy_level & secret_string l) * indexed_origins:secrecy_origin_list)

let secret_list : global_secrets_list_origins = []

(* Ghost function to return the content of the secret string *)
let secret_content (#l:secrecy_level) (s:secret_string l) : GTot string =
    match l with
    | PublicVal -> s
    | SecretVal ol ->
      let (AString #ol v) = s in v

(* Function to return the content of the secret string *)
private val get_string_from_secret : #l:secrecy_level -> s:secret_string l -> Tot (ns:string{ns = secret_content s})
let get_string_from_secret #l s =
    match l with
    | PublicVal -> s
    | SecretVal ol ->
      let (AString #ol v) = s in v

(* check if origin "o" is in list of secrecy_origins "l" *)
val is_origin_in_list_secrecy_origins : o:origin -> l:list secrecy_origin -> Tot (bool)
let rec is_origin_in_list_secrecy_origins o l =
    match l with
    | [] -> false
    | (SecOrigin hd)::tl -> (o = hd) || (is_origin_in_list_secrecy_origins o tl)
    | (OriginStar host)::tl -> (is_origin_match_origin_domain o host) || (is_origin_in_list_secrecy_origins o tl)

(* check if origin "o" is in list of secrecy_origins "l" *)
val is_origin_domain_in_list_secrecy_origins : o:origin_domain -> l:list secrecy_origin -> Tot (bool)
let rec is_origin_domain_in_list_secrecy_origins h l =
    match l with
    | [] -> false
    | (OriginStar host)::tl -> (origin_domain_match h host) || (is_origin_domain_in_list_secrecy_origins h tl)
    | _::tl -> (is_origin_domain_in_list_secrecy_origins h tl)

(* Checks if an origin (including domain checks for OriginStar) is a part of the secrecy level *)
val is_origin_secret_mem: o:origin -> l:secrecy_level{SecretVal? l} -> Tot (bool)
let is_origin_secret_mem o l = 		
    match l with
    | SecretVal ol -> is_origin_in_list_secrecy_origins o ol

(* is l a sublist of l' *)
val is_secrecy_origin_list_sublist : list secrecy_origin -> list secrecy_origin -> Tot bool
let rec is_secrecy_origin_list_sublist l l' =
  match l with 
  | [] -> true
  | (SecOrigin o)::tl -> is_origin_in_list_secrecy_origins o l' && is_secrecy_origin_list_sublist tl l'
  | hd::tl -> List.mem hd l' && is_secrecy_origin_list_sublist tl l'

(* Ghost function that checks if a secrecy level can be restricted to a more secret level *)
val can_restrict_secrecy_level : secrecy_level -> secrecy_level -> GTot bool
let can_restrict_secrecy_level l1 l2 = 
    (l1 = l2) ||
    (match l1,l2 with
    | PublicVal, l2 -> true
    | SecretVal ol, SecretVal ol' -> (if (List.length ol >= List.length ol') then list_is_sublist ol' ol else false) || is_secrecy_origin_list_sublist ol' ol
    | _, _ -> false)

(* a secrecy level can be restricted to itself *)
val restrict_secrecy_level_lemma : l1:secrecy_level -> 
				   l2:secrecy_level -> 
				   Lemma (requires (l1 = l2)) 
					 (ensures (can_restrict_secrecy_level l1 l2)) 
					 [SMTPat (can_restrict_secrecy_level l1 l2)]
let restrict_secrecy_level_lemma l1 l2 = ()

(* Function to classify_secret_string a string to a more secret level *)
val classify_secret_string : #l:secrecy_level -> 
			     s:secret_string l -> 
			     l':secrecy_level{can_restrict_secrecy_level l l'} -> 
			     Tot (t:secret_string l'{secret_content t = secret_content s})
let classify_secret_string #l s l' =
    match l,l' with
    | PublicVal,PublicVal -> s
    | PublicVal,SecretVal ol ->
        let a:a_string ol = AString #ol s in
	a
    | SecretVal ol,SecretVal [o] ->
       (match s with
        | AString #ol s ->
          let a:a_string [o] = AString #[o] s in
	  a)
    | SecretVal ol, SecretVal ol' ->
	(match s with
	| AString #ol s ->
	  let a:a_string ol' = AString #ol' s in
	  a)

(* Checks if the origin is a part of the secrecy level or if the secrecy level is public *)
val is_origin_in_secrecy_level : origin -> s:secrecy_level -> Tot bool
let is_origin_in_secrecy_level t s =
  match s with
  | PublicVal -> true
  | SecretVal sec -> is_origin_secret_mem t s





(* create a new secrecy level by adding a new origin *)
val add_origin_to_secrecy_level : s:secrecy_level -> o:secrecy_origin -> Tot (ns:secrecy_level{can_restrict_secrecy_level ns s})
let add_origin_to_secrecy_level s o = 
  match s with 
  | PublicVal -> PublicVal (* if the secrecy level was public, then remain public as we are decreasing the secrecy level *)
  | SecretVal ol -> let ol' = List.append ol [o] in SecretVal ol'

(* Checks if two secret strings of the same secrecy level are is_equal_secret_string *)
val is_equal_secret_string: #l:secrecy_level -> s:secret_string l -> t:secret_string l -> Tot (bool)
let is_equal_secret_string #l s t =
  match l with
  | PublicVal -> s = t
  | SecretVal ol ->
      let (AString #ol v1) = s in
      let (AString #ol v2) = t in
      v1 = v2
      
(* Returns the secret_string_length of the secret string *)
val secret_string_length: #l:secrecy_level -> s:secret_string l -> Tot (r:nat{r = String.length(secret_content #l s)})
let secret_string_length #l s = 
    match l with
    | PublicVal -> String.length s
    | SecretVal ol -> 
      (match s with 
       | AString #ol v -> String.length v)

(* Returns the substring of the secret string *)
val secret_string_substring : #l:secrecy_level -> s:secret_string l -> i:nat -> n:nat{i + n <= secret_string_length s} -> Tot (ns:(secret_string l){secret_string_length ns = n})
let secret_string_substring #l s i n =
    match l with
    | PublicVal -> substringImpl s i n (* String.make n (String.sub s i n) *)
    | SecretVal ol -> 
      (match s with 
       | AString #ol v -> AString #ol (substringImpl v i n (* String.make n (String.sub v i n) *)))

(* Concatenates two secret strings of the same secrecy level *)
val secret_string_strcat: #l:secrecy_level -> s:secret_string l -> t:secret_string l
    	    -> Tot (st:secret_string l{secret_content st = String.strcat (secret_content s) (secret_content t)})
let secret_string_strcat #l s t = 		
    match l with
    | PublicVal -> String.strcat s t
    | SecretVal ol -> 
      let (AString #ol v1) = s in
      let (AString #ol v2) = t in
           AString #ol (String.strcat v1 v2)

(* assume val randomString: (l:secrecy_level) -> (n:UInt32.t) -> ST (secret_string l) *)
(*        	   (requires (fun _ -> true)) *)
(* 	   (ensures  (fun h0 s h1 -> h0 == h1 /\ length #l s = UInt32.v n)) *)

(* val eqSecLevel : s1:secrecy_level -> s2:secrecy_level -> Tot bool *)
(* let eqSecLevel s1 s2 =  *)
(*   (s1 = s2) ||  *)
(*   (match s1 with  *)
(*   | PublicVal -> if (s2 = PublicVal) then true else false *)
(*   | SecretVal sec -> match s2 with *)
(* 		  | PublicVal -> false *)
(* 		  | SecretVal sec2 -> is_same_origin_in_list sec sec2) *)

val empty_secret_string : l:secrecy_level -> Tot (secret_string l)
let empty_secret_string l = (classify_secret_string #PublicVal "" l)

val is_secret_equal_public_string : #l:secrecy_level -> (s:secret_string l) -> p:(public_string) -> Tot (b:bool{b = (secret_content #PublicVal p = secret_content #l s)})
let is_secret_equal_public_string #l s p =
  match l with
  | PublicVal -> (s = p)
  | SecretVal ol ->
      let (AString #ol v) = s in (v = p)
      
val mk_list_secret_string : #s:secrecy_level -> list string -> Tot (list (secret_string s))
let rec mk_list_secret_string #s l =
  match l with
  | [] -> []
  | hd::tl -> (classify_secret_string #PublicVal hd s)::(mk_list_secret_string tl)

private val get_secret_origins_global_list : #l:secrecy_level -> secret_string l -> global_secrets_list_origins -> Tot (list secrecy_origin)
let rec get_secret_origins_global_list #l s ls =
  match ls with
  | [] -> []
  | ((|hl,hs|),lo)::tl -> if (hl = l && hs = s) then lo else get_secret_origins_global_list s tl

(* Reclassify_secret_string the string to an unrelated secrecy level *)
val can_reclassify_secret_string : #l:secrecy_level -> secret_string l -> l':secrecy_level -> GTot bool
let can_reclassify_secret_string #l s l' =
  (l = PublicVal) || (* If l is public already, it can be classified to any level *)
  (let lo = get_secret_origins_global_list #l s secret_list in 
  match l' with
  | PublicVal -> false
  | SecretVal ol' -> (List.for_all (fun x -> List.mem x lo) ol'))

val add_secret_origins_global_list : #l:secrecy_level -> s:secret_string l -> ol:secrecy_origin_list -> ls:global_secrets_list_origins -> Tot (nls:global_secrets_list_origins)
let rec add_secret_origins_global_list #l s ol ls = 
  match ls with
  | [] -> [((|l, s|), ol)]
  | ((|hl,hs|),lo)::tl -> if (hl = l && hs = s) then ((|hl,hs|), (List.append ol lo))::tl else ((|hl,hs|),lo)::(add_secret_origins_global_list s ol tl)

(* *** TODO - ALLOW restriction of subdomain to domain and http to https *** *)
val reclassify_secret_string : #l:secrecy_level -> s:secret_string l -> 
			       l':(secrecy_level){can_reclassify_secret_string #l s l'} -> 
			       Tot (t:(secret_string l'){secret_content t = secret_content s})
let reclassify_secret_string #l s l' =
    match l,l' with
    | PublicVal, PublicVal -> s
    | PublicVal, SecretVal ol -> classify_secret_string s l'	
    | SecretVal ol, PublicVal -> (match s with | AString #ol t -> t)
    | SecretVal ol, SecretVal ol' -> 
	(match s with | AString #ol s -> let a:a_string ol' = AString #ol' s in a)

(* Checks if the origin is a part of the secrecy level or if the secrecy level is public *)
let declassify_secret_string (#l:secrecy_level) (s:secret_string l) : Tot string = 
    match l with
    | PublicVal -> s
    | SecretVal ol -> 
      let (AString #ol v) = s in v

(* Server-side declassify_secret_string --- the server should be able to properly guess the secrecy_level for declassify_secret_string to succeed *)
let s_declassify_secret_string (l:secrecy_level) (s:secret_string l) : Tot string = 
    match l with
    | PublicVal -> s
    | SecretVal ol -> let (AString #ol v) = s in v

let rec declassify_list_secret_string  (#l:secrecy_level) (s:list (secret_string l)) : Tot (list string) = 
  match s with 
  | [] -> []
  | hd::tl -> (declassify_secret_string #l hd)::(declassify_list_secret_string tl)


