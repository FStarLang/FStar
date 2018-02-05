(*
  Defines the structure of URI (origin, path, querystring, fragment)
*)

module Web.URI

open Web.Origin
open Secret.SecString
open AuxiliaryFunctions 

module List = FStar.List.Tot

type path (l:secrecy_level) = list (secret_string l)
type querystring (l:secrecy_level) = list ((secret_string l) * (secret_string l))
type fragment (l:secrecy_level) = secret_string l

(* origin/path?querystring#fragment e.g. https://cnn.com:443/a/b/c/?x=1&y=2#t=3 *)
(* c_uri represents the actual uri *)
type c_uri (s:secrecy_level) = {
  uri_origin:origin_tuple;
  uri_username:secret_string s;
  uri_password:secret_string s;
  uri_path:path s;
  uri_querystring:querystring s;
  uri_fragment:fragment s
}

(* The domain of URI should be a part of the list of origins to enable access to the URI *)
private val is_uri_secrecy_level_valid : #s:secrecy_level -> u:c_uri s -> GTot bool
let is_uri_secrecy_level_valid #s u = is_origin_in_secrecy_level u.uri_origin s

(* abstract representation of the uri *)
type a_uri (s:secrecy_level) = u:(c_uri s){is_uri_secrecy_level_valid u}

type uri =
| URI : uri_secrecy_level:secrecy_level -> uri_value:a_uri uri_secrecy_level -> uri 

(* *** URI functions *** *)
val blank_curi : #s:secrecy_level{s = PublicVal} -> Tot (c_uri s)
let blank_curi #s = {uri_origin=blank_origin;
		    uri_username="";
		    uri_password="";
		    uri_path=[];
		    uri_querystring=[];
		    uri_fragment=""}

val mk_a_uri : #s:secrecy_level -> c:c_uri s{is_uri_secrecy_level_valid c} -> Tot (a_uri s)
let mk_a_uri #s c = c

val mk_uri : #s:secrecy_level -> (a_uri s) -> Tot uri
let mk_uri #s u = URI s u

val mk_c_uri : #s:secrecy_level -> (a_uri s) -> Tot (c_uri s)
let mk_c_uri #s u = u

val classify_uri_querystring : #s:secrecy_level -> querystring s -> s':secrecy_level{can_restrict_secrecy_level s s'} -> Tot (querystring s')
let rec classify_uri_querystring #s l s' = 
  match l with
  | [] -> []
  | (hq,hv)::tl -> (classify_secret_string #s hq s', classify_secret_string #s hv s')::(classify_uri_querystring tl s')

val classify_uri_path : #s:secrecy_level -> path s -> s':secrecy_level{can_restrict_secrecy_level s s'} -> Tot (path s')
let rec classify_uri_path #s l s' = 
  match l with
  | [] -> []
  | hd::tl -> (classify_secret_string #s hd s')::(classify_uri_path tl s') 

val get_uri_querystring : #s:secrecy_level -> u:uri{URI?.uri_secrecy_level u = s} -> Tot (querystring s)
let get_uri_querystring #s u = (URI?.uri_value u).uri_querystring

val get_uri_path : #s:secrecy_level -> u:uri{URI?.uri_secrecy_level u = s} -> Tot (path s)
let get_uri_path #s u = (URI?.uri_value u).uri_path

private val is_path_equal : #s:secrecy_level -> path s -> path s -> Tot bool
let rec is_path_equal #s l l' =
  match l with
  | [] -> (match l' with 
	 | [] -> true
	 | _ -> false)
  | hd::tl -> (match l' with
	    | [] -> false
	    | hd'::tl' -> is_equal_secret_string hd hd' && is_path_equal tl tl')

private val is_querystring_equal : #s:secrecy_level -> querystring s -> querystring s -> Tot bool
let rec is_querystring_equal #s l l' =
  match l with
  | [] -> (match l' with 
	 | [] -> true
	 | _ -> false)
  | (hq,hv)::tl -> (match l' with
		 | [] -> false
		 | (hq',hv')::tl' -> is_equal_secret_string hq hq' && is_equal_secret_string hv hv' && is_querystring_equal tl tl')

val is_uri_equal : uri -> uri -> bool -> Tot (bool)
let is_uri_equal a b ef =
    (URI?.uri_secrecy_level a = URI?.uri_secrecy_level b) &&
    (URI?.uri_value a).uri_origin = (URI?.uri_value b).uri_origin && 
    is_equal_secret_string ((URI?.uri_value a).uri_username) ((URI?.uri_value b).uri_username) && 
    is_equal_secret_string ((URI?.uri_value a).uri_password) ((URI?.uri_value b).uri_password) && 
    is_path_equal ((URI?.uri_value a).uri_path) ((URI?.uri_value b).uri_path) && 
    is_querystring_equal ((URI?.uri_value a).uri_querystring) ((URI?.uri_value b).uri_querystring) &&
    (if ef = false then is_equal_secret_string #(URI?.uri_secrecy_level a) ((URI?.uri_value a).uri_fragment) ((URI?.uri_value b).uri_fragment) else true)
        
val serialize_querystring : #s:secrecy_level -> querystring s -> Tot (secret_string s)
let rec serialize_querystring #s q =
  match q with
  | [] -> empty_secret_string s
  | (hf, hs)::tl -> 
    if (not (is_equal_secret_string hf (empty_secret_string s))) then (* the query key should not be empty string *)
       secret_string_strcat (secret_string_strcat (secret_string_strcat hf (classify_secret_string #PublicVal "=" s)) hs) 
	      (if tl = [] then (empty_secret_string s) else (secret_string_strcat (classify_secret_string #PublicVal "&" s) (serialize_querystring tl)))
    else 
       (if tl = [] then (empty_secret_string s) else (secret_string_strcat (classify_secret_string #PublicVal "&" s) (serialize_querystring tl)))
		    
val username_password_to_string : #s:secrecy_level -> secret_string s -> secret_string s -> Tot (secret_string s)
let username_password_to_string #s u p = (* strcat (strcat (strcat u (classify_secret_string #PublicVal ":" s)) p) (classify_secret_string #PublicVal "@" s) *)
  if (u = empty_secret_string s) then (empty_secret_string s)
  else (
    if (p = empty_secret_string s) then secret_string_strcat u (secret_string_strcat (classify_secret_string #PublicVal ":" s) (classify_secret_string #PublicVal "@" s))
    else secret_string_strcat u (secret_string_strcat (classify_secret_string #PublicVal ":" s) (secret_string_strcat p (classify_secret_string #PublicVal "@" s)))
  )

val path_to_string : #s:secrecy_level -> list (secret_string s) -> Tot (secret_string s)
let rec path_to_string #s p = 
  match p with 
  | [] -> classify_secret_string #PublicVal "/" s 
  | h::t -> if (not (is_equal_secret_string h (empty_secret_string s))) then 
	     secret_string_strcat (secret_string_strcat (classify_secret_string #PublicVal "/" s) h) (path_to_string t) 
	  else (path_to_string t)

val uri_to_secret_string : #s:secrecy_level -> c_uri s -> Tot (secret_string s) //partial inverse of the hstring_to_curi
let uri_to_secret_string #s u = 
  match (u.uri_origin) with
  | Origin pr h p d -> (secret_string_strcat (secret_string_strcat (secret_string_strcat (secret_string_strcat (secret_string_strcat 
		      (classify_secret_string #PublicVal (pr ^ "://") s) (username_password_to_string u.uri_username u.uri_password)) 
		      (classify_secret_string #PublicVal ((origin_domain_to_string h) ^ 
		      (if p <> None then ":" ^ string_of_int (Some?.v p) else "")) s)) (path_to_string u.uri_path))
		      (if u.uri_querystring = [] then (empty_secret_string s) 
		      else (secret_string_strcat (classify_secret_string #PublicVal "?" s) (serialize_querystring u.uri_querystring)))) 
		      (secret_string_strcat (classify_secret_string #PublicVal "#" s) u.uri_fragment))

(* Only for debugging - printing and logging *)
val uri_to_string : uri -> Tot (string)
let uri_to_string u = declassify_secret_string (uri_to_secret_string #(URI?.uri_secrecy_level u) (URI?.uri_value u))

