(*
  Defines the origin of a uri (scheme, domain, port)
*)

module Web.Origin

open AuxiliaryFunctions

module List = FStar.List.Tot

(* Other schemes are also used when checking (ftp, ws, data etc.) - Adding as necessary*)
type scheme = s:string{s="" || s="http" || s="https" || s="javascript" || s="ftp" || s="ws" || s="data"}
  
type hstring = string //= s:string{forall i. not (List.mem (String.get s i) ['.';'&';'=';':';'/';'\\'])}
type hdomain = list hstring
type port = int

(* protocol://host:port e.g. https://cnn.com:443 *)
(* OOrigin -> opaque domain a unique domain for every opaque domain *)
type origin = 
| TOrigin : protocol:scheme -> host: hdomain -> port:option port -> dom:option hdomain -> origin
| OOrigin : id:nat -> origin

type torigin = o:origin{TOrigin? o}

let blank_origin = (TOrigin "" [] None None)

val isProtocol : string -> Tot bool
let isProtocol s = (s="" || s="http" || s="https" || s="javascript" || s="ftp" || s="ws" || s="data")

val hd_string : list string -> Tot string
let rec hd_string hd = 
  match hd with 
  | [] -> ""
  | h::t -> h ^ (if t = [] then "" else "." ^ (hd_string t))

val origin_to_string : origin -> Tot string
let origin_to_string o = 
    match o with 
    | OOrigin _ -> ""
    | TOrigin s h p d -> (s ^ "://" ^ (hd_string h) ^ (if p <> None then ":" ^ string_of_int (Some?.v p) else ""))  

(* bad port - 3.5 Fetch spec *)
val port_is_bad : port -> Tot bool
let port_is_bad p = (p=1 || p=7 || p=9 || p=11 || p=13 || p=15 || p=17 || p=19 || p=20 || p=21 || p=22 || p=23 || p=25 || p=37 || p=42 || p=43 || p=53 || p=77 || p=79 || p=87 || p=95 || p=101 || p=102 || p=103 || p=104 || p=109 || p=110 || p=111 || p=113 || p=115 || p=117 || p=119 || p=123 || p=135 || p=139 || p=143 || p=179 || p=389 || p=465 || p=512 || p=513 || p=514 || p=515 || p=526 || p=530 || p=531 || p=532 || p=540 || p=556 || p=563 || p=587 || p=601 || p=636 || p=993 || p=995 || p=2049 || p=3659 || p=4045 || p=6000 || p=6665 || p=6666 || p=6667 || p=6668 || p=6669)

(* Section 7.5 HTML 5.1 sameorigin *)
val isSameOrigin: origin -> origin -> Tot bool
let isSameOrigin o0 o1 = 
  match o0 with 
  | OOrigin n -> if (o1 = OOrigin n) then true else false
  | TOrigin s0 h0 p0 _ -> match o1 with 
	      | OOrigin _ -> false
	      | TOrigin s1 h1 p1 _ -> (s0 = s1 && h0 = h1 && p0 = p1)

(* Section 7.5 HTML 5.1 sameorigindomain *)
val isSameOriginDom: origin -> origin -> Tot bool
let isSameOriginDom o0 o1 = 
  (o0 = o1) || 
  (match o0 with 
  | OOrigin n -> if (o1 = OOrigin n) then true else false
  | TOrigin s0 h0 p0 d0 -> match o1 with 
	      | OOrigin _ -> false
	      | TOrigin s1 h1 p1 d1 -> 
		  if (s0 = s1 && d0 = d1 && d0 <> None) then true
		  else if ((isSameOrigin o0 o1) && d0 = None && d1 = None) then true
		  else false)

(* is Same origin in the list of origins *)
val isSameOriginListOrig: torigin -> list torigin -> Tot bool
let rec isSameOriginListOrig o l = (List.mem o l) ||
  (match l with
  | [] -> false
  | hd::tl -> (isSameOriginDom o hd) || (isSameOriginListOrig o tl))

(* is Same origin in the list of origins *)
val isSameOriginList: list torigin -> list torigin -> Tot bool
let rec isSameOriginList l l' =
  match l with
  | [] -> false
  | hd::tl -> (isSameOriginListOrig hd l') || (isSameOriginList tl l')

(* Check if list in h is a sub-sequence of list in l *)
val dMatch : list string -> list string -> Tot bool
let rec dMatch l h =
  match h with
  | [] -> true
  | hd::tl -> if hd = "*" then true
	    else 
	      match l with
	      | [] -> false
	      | hl::tll -> if hd = hl then dMatch tll tl
			 else false

(* As hdomain is a list of strings where each string contains of only characters without periods, 
   it suffices to check if the complete second list is present in the first list. 
   For a reversed list, the second list is prefix of the first list
   -- h domain-matches d 
*)
(* Is the origin "h" a subdomain of d, i.e., is "d" a suffix of "h" *)
val domainMatch : hdomain -> hdomain -> Tot bool
let domainMatch h d = 
  let od = List.rev h in
  let hd = List.rev d in 
  (h = d) || (dMatch od hd)

(* Match an origin with list of domains *)
val hostMatch : hdomain -> list hdomain -> Tot bool
let rec hostMatch h l =
  match l with
  | [] -> false
  | hd::tl -> if (domainMatch h hd) then true
	    else hostMatch h tl 
  
