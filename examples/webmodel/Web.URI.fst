(*
  Defines the structure of URI (origin, path, querystring, fragment)
*)

module Web.URI

open Web.Origin
open Secret.SecString
open AuxiliaryFunctions 

module List = FStar.List.Tot

type path (l:secLevel) = list (secString l)
type querystring (l:secLevel) = list ((secString l) * (secString l))
type fragment (l:secLevel) = secString l

(* origin/path?querystring#fragment e.g. https://cnn.com:443/a/b/c/?x=1&y=2#t=3 *)
type c_uri (s:secLevel) = {
  c_origin:torigin;
  c_uname:secString s;
  c_pwd:secString s;
  c_path:path s;
  c_querystring:querystring s;
  c_fragment:fragment s
}

(* abstract type a_uri (s:secLevel) = c:c_uri{match s with | PublicVal -> true | SecretVal sec -> isSameOriginListOrig c.c_origin sec} *)

(* check for valid origin in the index of secrets - check only the protocol and the host domain *)
(* private val isValidOrigin : list torigin -> torigin -> Tot bool *)
(* let rec isValidOrigin ls o =  *)
(*   match ls with *)
(*   | [] -> false *)
(*   | hd::tl -> if (TOrigin?.protocol hd) = (TOrigin?.protocol o) && (TOrigin?.host hd) = (TOrigin?.host o) then true *)
(* 	    else isValidOrigin tl o *)

(* The domain of URI should be a part of the list of origins to enable access to the URI *)
val isValidURI : #s:secLevel -> c_uri s -> GTot bool
let isValidURI #s c =
  match s with 
  | PublicVal -> true 
  | SecretVal sec -> List.mem c.c_origin sec (*isSameOriginListOrig c.c_origin sec *)

type a_uri (s:secLevel) = c:(c_uri s){isValidURI c}

type uri =
| URI : usl:secLevel -> u:a_uri usl -> uri 

(* private val u_curi : uri -> Tot c_uri  *)
(* let u_curi u = match u with | URI l loc -> loc *)

(* *** URI *** *)
val blank_curi : #s:secLevel{s = PublicVal} -> Tot (c_uri s)
let blank_curi #s = {c_origin=blank_origin;c_uname="";c_pwd="";c_path=[];c_querystring=[];c_fragment=""}

val mk_auri : #s:secLevel -> c:c_uri s{isValidURI c} -> Tot (a_uri s)
let mk_auri #s c = c

val mk_uri : #s:secLevel -> (a_uri s) -> Tot uri
let mk_uri #s u = URI s u

val mk_curi : #s:secLevel -> (a_uri s) -> Tot (c_uri s)
let mk_curi #s u = u

val classifyQS : #s:secLevel -> querystring s -> s':secLevel{restricts s s'} -> Tot (querystring s')
let rec classifyQS #s l s' = 
  match l with
  | [] -> []
  | (hq,hv)::tl -> (classify #s hq s', classify #s hv s')::(classifyQS tl s')

val classifyPath : #s:secLevel -> path s -> s':secLevel{restricts s s'} -> Tot (path s')
let rec classifyPath #s l s' = 
  match l with
  | [] -> []
  | hd::tl -> (classify #s hd s')::(classifyPath tl s') 

val getQS : #s:secLevel -> u:uri{URI?.usl u = s} -> Tot (querystring s)
let getQS #s u = (URI?.u u).c_querystring

val getPathVal : #s:secLevel -> u:uri{URI?.usl u = s} -> Tot (path s)
let getPathVal #s u = (URI?.u u).c_path

private val equalPath : #s:secLevel -> path s -> path s -> Tot bool
let rec equalPath #s l l' =
  match l with
  | [] -> (match l' with 
	 | [] -> true
	 | _ -> false)
  | hd::tl -> (match l' with
	    | [] -> false
	    | hd'::tl' -> equal hd hd' && equalPath tl tl')

private val equalQS : #s:secLevel -> querystring s -> querystring s -> Tot bool
let rec equalQS #s l l' =
  match l with
  | [] -> (match l' with 
	 | [] -> true
	 | _ -> false)
  | (hq,hv)::tl -> (match l' with
	    | [] -> false
	    | (hq',hv')::tl' -> equal hq hq' && equal hv hv' && equalQS tl tl')

val equalURL : uri -> uri -> bool -> Tot (bool)
let equalURL a b ef =
    (URI?.usl a = URI?.usl b) &&
    (URI?.u a).c_origin = (URI?.u b).c_origin && 
    equal ((URI?.u a).c_uname) ((URI?.u b).c_uname) && 
    equal ((URI?.u a).c_pwd) ((URI?.u b).c_pwd) && 
    equalPath ((URI?.u a).c_path) ((URI?.u b).c_path) && 
    equalQS ((URI?.u a).c_querystring) ((URI?.u b).c_querystring) &&
    (if ef = false then equal #(URI?.usl a) ((URI?.u a).c_fragment) ((URI?.u b).c_fragment) else true)
        
val serializeQueryString : #s:secLevel -> querystring s -> Tot (secString s)
let rec serializeQueryString #s q =
  match q with
  | [] -> emptyString s
  | (hf, hs)::tl -> 
    if (not (eqString hf "")) then (* the query key should not be empty string *)
       strcat (strcat (strcat hf (classify #PublicVal "=" s)) hs) (if tl = [] then (emptyString s) else (strcat (classify #PublicVal "&" s) (serializeQueryString tl)))
    else 
       (if tl = [] then (emptyString s) else (strcat (classify #PublicVal "&" s) (serializeQueryString tl)))
		    
val uname_pwd_string : #s:secLevel -> secString s -> secString s -> Tot (secString s)
let uname_pwd_string #s u p = (* strcat (strcat (strcat u (classify #PublicVal ":" s)) p) (classify #PublicVal "@" s) *)
  if (u = emptyString s) then (emptyString s)
  else (
    if (p = emptyString s) then strcat u (strcat (classify #PublicVal ":" s) (classify #PublicVal "@" s))
    else strcat u (strcat (classify #PublicVal ":" s) (strcat p (classify #PublicVal "@" s)))
  )

val path_string : #s:secLevel -> list (secString s) -> Tot (secString s)
let rec path_string #s p = 
  match p with 
  | [] -> classify #PublicVal "/" s 
  | h::t -> if (not (eqString h "")) then strcat (strcat (classify #PublicVal "/" s) h) (path_string t) 
	  else (path_string t)
	  (* (if t = [] then (classify #PublicVal "/" s) else strcat (classify #PublicVal "/" s) (path_string t)) *)

val curi_to_hstring : #s:secLevel -> c_uri s -> Tot (secString s) //partial inverse of the hstring_to_curi
let curi_to_hstring #s u = 
  match (u.c_origin) with
  | TOrigin pr h p d -> (strcat (strcat (strcat (strcat (strcat (classify #PublicVal (pr ^ "://") s) (uname_pwd_string u.c_uname u.c_pwd)) 
      (classify #PublicVal ((hd_string h) ^ 
      (if p <> None then ":" ^ string_of_int (Some?.v p) else "")) s)) (path_string u.c_path))
      (if u.c_querystring = [] then (emptyString s) else (strcat (classify #PublicVal "?" s) (serializeQueryString u.c_querystring)))) 
      (strcat (classify #PublicVal "#" s) u.c_fragment))

(* Only for debugging - printing and logging *)
val uri_to_hstring_val : uri -> Tot (string)
let uri_to_hstring_val u = declassify (curi_to_hstring #(URI?.usl u) (URI?.u u))

