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

(* Secrecy level *)
type secLevel = 
| PublicVal : secLevel
| SecretVal : seco:list torigin{not (emptyList seco)} -> secLevel

(* abstract *) 
type a_string (ol:list torigin) = 
     | AString : string -> a_string ol

let secString (s:secLevel): Tot Type0 =
     match s with
     | PublicVal -> string
     | SecretVal ol -> a_string ol

type pubString = secString PublicVal

(* all secrets with possible list of origins for a particular user *)
type secretOriginList = list ((l:secLevel & secString l) * list torigin)

let secList : secretOriginList = []

(* Ghost function to return the content of the secret string *)
let content (#l:secLevel) (s:secString l) : GTot string =
    match l with
    | PublicVal -> s
    | SecretVal ol ->
      let (AString #ol v) = s in v

(* Function to return the content of the secret string *)
private val getSecString : #l:secLevel -> ss:secString l -> Tot (ns:string{ns = content ss})
let getSecString #l s =
    match l with
    | PublicVal -> s
    | SecretVal ol ->
      let (AString #ol v) = s in v

(* Ghost function that checks if a secrecy level can be restricted to a more secret level *)
val restricts: l:secLevel -> l':secLevel -> GTot bool
let restricts l1 l2 =
    match l1,l2 with
    | PublicVal, l2 -> true
    | SecretVal ol, SecretVal [o] -> List.mem o ol
    | SecretVal ol, SecretVal ol' -> isSublist ol' ol
    | _, _ -> false

(* Function to classify a string to a more secret level *)
val classify: #l:secLevel -> s:secString l -> l':secLevel{restricts l l'} -> Tot (t:secString l'{content t = content s})
let classify #l s l' =
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

(* Returns the length of the secret string *)
val length: #l:secLevel -> s:secString l -> Tot (r:nat{r = String.length(content #l s)})
let length #l s =
    match l with
    | PublicVal -> String.length s
    | SecretVal ol ->
      (match s with
       | AString #ol v -> String.length v)

(* Returns the substring of the secret string *)
val substr : #l:secLevel -> s:secString l -> i:nat -> n:nat{i + n <= length s} -> Tot (ns:(secString l){length ns = n})
let substr #l s i n =
    match l with
    | PublicVal -> substringImpl s i n (* String.make n (String.sub s i n) *)
    | SecretVal ol ->
      (match s with
       | AString #ol v -> AString #ol (substringImpl v i n (* String.make n (String.sub v i n) *)))

(* Concatenates two secret strings of the same secrecy level *)
val strcat: #l:secLevel -> s:secString l -> t:secString l
    	    -> Tot (st:secString l{content st = String.strcat (content s) (content t)})
let strcat #l s t =
    match l with
    | PublicVal -> String.strcat s t
    | SecretVal ol ->
      let (AString #ol v1) = s in
      let (AString #ol v2) = t in
           AString #ol (String.strcat v1 v2)

(* Checks if two secret strings of the same secrecy level are equal *)
val equal: #l:secLevel -> s:secString l -> t:secString l -> Tot (bool)
let equal #l s t =
  match l with
  | PublicVal -> s = t
  | SecretVal ol ->
      let (AString #ol v1) = s in
      let (AString #ol v2) = t in
      v1 = v2
      
(* assume val randomString: (l:secLevel) -> (n:UInt32.t) -> ST (secString l) *)
(*        	   (requires (fun _ -> true)) *)
(* 	   (ensures  (fun h0 s h1 -> h0 == h1 /\ length #l s = UInt32.v n)) *)

(* s1 contains a sublist of s2 *)
val equalSubLevels : s1:secLevel -> s2:secLevel -> GTot (b:bool)
let equalSubLevels s1 s2 =
  (match s1,s2 with
  | PublicVal, PublicVal -> true
  | SecretVal sec, SecretVal sec' -> isSublist sec sec'
  | _, _ -> false
  )

val subLevel_lemma : s1:secLevel -> s2:secLevel -> Lemma (requires (equalSubLevels s1 s2)) (ensures (restricts s2 s1)) [SMTPat (equalSubLevels s1 s2)]
let subLevel_lemma s1 s2 = ()
  
(* val eqSecLevel : s1:secLevel -> s2:secLevel -> Tot bool *)
(* let eqSecLevel s1 s2 =  *)
(*   (s1 = s2) ||  *)
(*   (match s1 with  *)
(*   | PublicVal -> if (s2 = PublicVal) then true else false *)
(*   | SecretVal sec -> match s2 with *)
(* 		  | PublicVal -> false *)
(* 		  | SecretVal sec2 -> isSameOriginList sec sec2) *)

val emptyString : l:secLevel -> Tot (secString l)
let emptyString l = (classify #PublicVal "" l)

val eqString : #l:secLevel -> (s:secString l) -> p:(pubString) -> Tot (b:bool{b = (content #PublicVal p = content #l s)})
let eqString #l s p =
  match l with
  | PublicVal -> (s = p)
  | SecretVal ol ->
      let (AString #ol v) = s in (v = p)
      
val mk_list_string : #s:secLevel -> list string -> Tot (list (secString s))
let rec mk_list_string #s l =
  match l with
  | [] -> []
  | hd::tl -> (classify #PublicVal hd s)::(mk_list_string tl)

(* Checks if the origin is a part of the secrecy level or if the secrecy level is public *)
val isOriginSec : torigin -> s:secLevel -> Tot bool
let isOriginSec t s =
  match s with
  | PublicVal -> true
  | SecretVal sec -> List.mem t sec

private val getSecretOrigin : #l:secLevel -> secString l -> secretOriginList -> Tot (list torigin)
let rec getSecretOrigin #l s ls =
  match ls with
  | [] -> []
  | ((|hl,hs|),lo)::tl -> if (hl = l && hs = s) then lo else getSecretOrigin s tl

(* Reclassify the string to an unrelated secrecy level *)
val canReclassify : #l:secLevel -> secString l -> l':secLevel -> secretOriginList -> Tot bool
let canReclassify #l s l' ls =
  (l = PublicVal) || (* If l is public already, it can be classified to any level *)
  (let lo = getSecretOrigin #l s ls in
  match l' with
  | PublicVal -> false
  | SecretVal ol' -> (List.for_all (fun x -> List.mem x lo) ol'))

val addSecretOrigins : #l:secLevel -> s:secString l -> ol:list torigin -> ls:secretOriginList -> Tot (nls:secretOriginList)
let rec addSecretOrigins #l s ol ls =
  match ls with
  | [] -> [((|l, s|), ol)]
  | ((|hl,hs|),lo)::tl -> if (hl = l && hs = s) then ((|hl,hs|), (List.append ol lo))::tl else ((|hl,hs|),lo)::(addSecretOrigins s ol tl)

val reclassify : #l:secLevel -> s:secString l -> l':(secLevel) -> ls:secretOriginList{canReclassify #l s l' ls} -> Tot (t:(secString l'){content t = content s})
let reclassify #l s l' ls =
    match l,l' with
    | PublicVal, PublicVal -> s
    | PublicVal, SecretVal ol -> classify s l'
    | SecretVal ol, PublicVal -> (match s with | AString #ol t -> t)
    | SecretVal ol, SecretVal ol' ->
	(match s with | AString #ol s -> let a:a_string ol' = AString #ol' s in a)

(* Declassify a secret string *)
let declassify (#l:secLevel) (s:secString l) : Tot string =
    match l with
    | PublicVal -> s
    | SecretVal ol ->
      let (AString #ol v) = s in v

let rec declassify_list  (#l:secLevel) (s:list (secString l)) : Tot (list string) =
  match s with
  | [] -> []
  | hd::tl -> (declassify #l hd)::(declassify_list tl)

(* for printing and logging *)
val getOriginString : list torigin -> Tot (string)
let rec getOriginString l =
  match l with
  | [] -> ""
  | hd::tl -> "Origin: " ^ (origin_to_string hd) ^ "\n" ^ (getOriginString tl)
  
