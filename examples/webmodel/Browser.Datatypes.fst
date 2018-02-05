(*
  Defines the various data structures related to the browser 
  --- document, history, window, localstorage, request, response and the browser itself
  Also defines functions related to these data structures.  
*)

module Browser.Datatypes

open Web.Origin
open Secret.SecString 
open AuxiliaryFunctions 
open Web.URI
open Browser.AuxiliaryDatatypes
open Browser.StringFunctions
open ML.ExternalFunctions

module List = FStar.List.Tot

abstract type wid = nat

abstract type a_origin = o:origin
  
type document = {
  dloc:uri;
  dref:uri;
  dori:a_origin;
  dHTTPS:httpstate;
  drefPol:referrer_policy;
  dCSP:csp_policy;
  dsbox:list sandbox_flags;
}

abstract type a_document = document

(* For now, every history entry contains the minimal information, i.e., the url of the page*)
(* It may also contain state, title, document, form-data, scroll-restoration, scroll position, name etc.*)
type historyEntry = 
| HistEntry : hsl:secrecy_level -> heurl:a_uri hsl -> hetime:nat -> hedoc:document -> hewin:wid -> historyEntry

type historyFormat = {
  hlhe: list historyEntry;
  hcur: nat;
}

type history = h:historyFormat{h.hcur <= List.length h.hlhe}

abstract type a_history = history

val ahist_to_hist : a_history -> Tot history
let ahist_to_hist a = a

let emptyHistory = {hlhe=[];hcur=0}

type localStorageEntry = 
| LocalStorageEntry : lsb:origin_opaque ->
		      ls_origin:origin_tuple -> 
		      ldict:(dictionary #(secret_string (SecretVal [SecOrigin ls_origin])) #(secret_string (SecretVal [SecOrigin ls_origin]))) -> localStorageEntry

type cowindow' (bid:origin_opaque) = {
  cwinid:wid;
  cwname:public_string;
  cwloc:uri;
  cwframes:list (cowindow' bid);
  cwopener:option (cowindow' bid);
  cwparent:option (cowindow' bid);
  cwhist:a_history;
  cwdoc:a_document;
  cwsbox:list sandbox_flags;
}

type cowindow =
| CWindow : cwbid:origin_opaque -> cwin:(cowindow' cwbid) -> cowindow

(* type cowindow = *)
(* | CWindow : cwbid:origin_opaque -> cwin:(cowindow' cwbid){forall x. List.mem x (ahist_to_hist cwin.cwhist).hlhe ==> (x.hewin = cwin.cwinid)} -> cowindow *)

type window' (bid:origin_opaque) = {
  winid:wid;
  wname:public_string;
  wloc:uri;
  wframes:list (c:cowindow' bid);
  wopener:option (c:cowindow' bid);
  wparent:option (c:cowindow' bid);
  whist:history;
  wdoc:document;
  wsbox:list sandbox_flags;
}

(* all history entries should have the window id as the current window's id *)
(* type window = w:window'{ is_same_origin_domain (Doc.dsl w.wdoc).sori (w.wloc.uri_origin) /\   *)

type window = 
| Window : wbid: origin_opaque -> w:(window' wbid) -> window

(* Referer (sic) corresponding to referer header*)
type referer=
| NoReferrer
| Client of cowindow
| URLReferrer of uri 

(* A request can have a lot of associated fields as pointed out in 3.1.5 of Fetch spec (fetch.spec.whatwg.org). We model only few interesting ones here.
   Current URL is the first url in requrl
*)
type requestFormat (s:secrecy_level) = {
  reqbrowser:origin_opaque;
  reqm:reqMethod; (* request method - GET, POST, etc. *)
  requrl:list uri; (* first element in the list is the request uri *)
  reqhead:header; (* list of (header fields * header value) *)
  reqo:a_origin; (* origin of the window from which the request originated *)
  reqw:option (cowindow); (* window from which the request originated *)
  reqinit:initiator; 
  reqtype:requesttype;
  reqdest:destination;
  reqtarget:option (cowindow); (* target window for the request*)
  reqredirect:nat; (* count of number of redirects *)
  reqredmode:redirectVal;
  reqref:referer;
  reqreferrer_policy:referrer_policy;
  reqnonce:public_string;
  reqparser:parserVal;
  requnsafe:bool;
  reqpreflight:bool;
  reqsync:bool;
  reqmode:mode; (* mode represents whether or not the request is same-origin *)
  reqtaint:taintVal;
  reqcredm:credmode;
  reqcredflag:bool;
  reqbody:secret_string s;
  corsflag:bool;
  corspfflag:bool;
  authflag:bool;
  recflag:bool;
}

private val getOrigin : uri -> Tot origin_tuple
let getOrigin u = u.uri_value.uri_origin

(* construct a valid request to be sent on the network *)
val isValidBrowserRequest : #s:secrecy_level -> rf:requestFormat s -> GTot bool
let isValidBrowserRequest #s rf = 
  if (list_is_empty rf.requrl) then false
  else 
    let u = (List.hd rf.requrl) in 
    (can_restrict_secrecy_level u.uri_secrecy_level s) && 
    (checkHeaderSecLevel rf.reqhead) &&
    (isHeaderVisible rf.reqhead s) &&
    (is_origin_in_secrecy_level rf.reqbrowser u.uri_secrecy_level) &&
    (is_origin_in_secrecy_level rf.reqbrowser s)
    
type browserRequest = 
| BrowserRequest : breq_secrecy_level:secrecy_level -> 
		   browser_request:(requestFormat breq_secrecy_level){isValidBrowserRequest browser_request} -> browserRequest

(* logging msgs being sent out of the browser *)
type outMsg =
| HTTPReqMsg : r:browserRequest -> outMsg
| JSMsg : l:secrecy_level -> u:uri{u.uri_secrecy_level = l} -> s:secret_string l -> outMsg

val secOutMsg : outMsg -> Tot bool
let secOutMsg m =  match m with
  | HTTPReqMsg r -> true
  | JSMsg l u s -> true

type logMsg = o:outMsg{secOutMsg o}

(* Section 3.4 Fetch spec - Connections*)
type connection = {
  cori:origin_tuple;
  ccred:bool;
}

type connReq (b:origin_opaque) = {
  connect:connection;
  creq:list (r:browserRequest{r.browser_request.reqbrowser = b} * cowindow * cowindow * navType); (* windows required for processing response *)
}

(* type connectionPool = list connReq (\*contains the list of pending requests for that connection*\) *)

type browser' (bid:origin_opaque) : Type0 = {
  windows:list (cowindow' bid); 
  cookieStore:list (c:cookie{is_origin_in_secrecy_level bid c.cookie_secrecy_level});
  localStorage:list (ls:localStorageEntry{bid = ls.lsb});
  sts:list origin_domain;
  conn:list (connReq bid);
  next_u_id:wid;
}

type browser =
| Browser : bid:origin_opaque -> br:browser' bid -> browser

 



(* ***** INITIALIZE BROWSER ***** *)
let init_browser:browser = Browser (OpaqueOrigin 1) ({windows=[];cookieStore=[];localStorage=[];sts=[];conn=[];next_u_id=2})

(* Generate unique ids *)
val set_unique_id : browser -> Tot (wid * browser)
let set_unique_id b = (b.br.next_u_id, Browser b.bid ({b.br with next_u_id=(b.br.next_u_id + 1)}))

val set_op_origin : browser -> Tot (o:a_origin * browser)
let set_op_origin b = (OpaqueOrigin b.br.next_u_id, Browser b.bid ({b.br with next_u_id=(b.br.next_u_id + 1)}))

(* val noWindow : a_document -> Tot bool *)
(* let noWindow d = (d.dwin = 0) *)

val noWin : wid
let noWin = 0

(* let blank_doc = Document blank_uri blank_uri "none" RP_EmptyPolicy [] 0 [] "" *)
(* let blank_doc b = {dloc=blank_uri;dref=blank_uri;dori=OpaqueOrigin (get_unique_id b);dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=[];dwin=0;dsbox=[]} *)





(* ***** Functions for abstraction ***** *)
(* *** URI *** *)
private val get_c_uri : #s:secrecy_level -> b:browser -> sw:cowindow{b.bid = sw.cwbid} -> u:uri{u.uri_secrecy_level = s} -> Tot (option (c_uri s))
let get_c_uri #s b sw u =
  match u with
  | URI l loc -> if is_same_origin_domain (getOrigin sw.cwin.cwloc) loc.uri_origin then Some loc else None

val get_win_curi : #s:secrecy_level -> b:browser -> sw:cowindow{b.bid = sw.cwbid} -> 
		   tw:cowindow{tw.cwin.cwloc.uri_secrecy_level = s /\ b.bid = tw.cwbid} -> Tot (option (c_uri s))
let get_win_curi #s b sw tw = get_c_uri b sw (tw.cwin.cwloc)

private val reclassifyVal : #l:secrecy_level -> s:secret_string l -> l':(secrecy_level) -> Tot (t:(secret_string l'){secret_content t = secret_content s})
let reclassifyVal #l s l' =
    match l,l' with
    | PublicVal,PublicVal -> s
    | PublicVal,SecretVal ol -> classify_secret_string s l'	
    | SecretVal _,PublicVal -> declassify_secret_string s
    | SecretVal ol,SecretVal ol' -> 
	(match s with | AString #ol s -> let a:a_string ol' = AString #ol' s in a)
	
(* Some private reclassify_secret_string functions for URI's security level --- use reclassifyVal only here *) 
private val recPath : #s:secrecy_level -> path s -> s':secrecy_level -> Tot (path s')
let rec recPath #s l s' =
  match l with
  | [] -> []
  | hd::tl -> (reclassifyVal hd s')::(recPath tl s')

val classify_uri_path : #s:secrecy_level -> path s -> s':secrecy_level{can_restrict_secrecy_level s s'} -> Tot (path s')
let classify_uri_path #s l s' =
  match l with
  | [] -> []
  | hd::tl -> (classify_secret_string hd s')::(classify_uri_path tl s')

private val recQS : #s:secrecy_level -> querystring s -> s':secrecy_level -> Tot (querystring s')
let rec recQS #s l s' =
  match l with
  | [] -> []
  | (hq,hv)::tl -> (reclassifyVal hq s', reclassifyVal hv s')::(recQS tl s')

val classify_uri_querystring : #s:secrecy_level -> querystring s -> s':secrecy_level{can_restrict_secrecy_level s s'} -> Tot (querystring s')
let rec classify_uri_querystring #s l s' =
  match l with
  | [] -> []
  | (hq,hv)::tl -> (classify_secret_string hq s', classify_secret_string hv s')::(classify_uri_querystring tl s')

val u_curi : #s:secrecy_level -> u:uri{u.uri_secrecy_level = s} -> Tot (c_uri s)
let u_curi #s u = mk_c_uri u.uri_value

val equalAOrigin : a_origin -> a_origin -> Tot bool
let equalAOrigin a0 a1 = a0 = a1

val emptyFragment : u:uri -> Tot bool
let emptyFragment u = is_equal_secret_string #u.uri_secrecy_level u.uri_value.uri_fragment (empty_secret_string u.uri_secrecy_level)

val getAOrigin : uri -> Tot a_origin
let getAOrigin u = u.uri_value.uri_origin

(* can allow restriction of subdomain? 
   a.b.com can be restricted to b.com *)
private val setDomOrigin : u:uri{Origin? u.uri_value.uri_origin} -> o:a_origin -> Tot uri
let setDomOrigin u o = 
  if (Origin? o) then 
    let os = (match u.uri_secrecy_level with
	     | PublicVal -> (PublicVal) (* Should we keep it Public? *)
	     | SecretVal ol -> (SecretVal ((SecOrigin o)::ol))) in (* reclassify_secret_string including the older origins - used in setDocumentDomain *)
    URI os ({uri_origin=o;
	   uri_username=reclassifyVal u.uri_value.uri_username os;
	   uri_password=reclassifyVal u.uri_value.uri_password os;
	   uri_path=recPath u.uri_value.uri_path os;
	   uri_querystring=recQS u.uri_value.uri_querystring os;
	   uri_fragment=reclassifyVal #u.uri_secrecy_level u.uri_value.uri_fragment os})
  else u

val getScheme : uri -> Tot origin_protocol
let getScheme u = (Origin?.protocol u.uri_value.uri_origin)

val getPort : uri -> Tot (option origin_port)
let getPort u = (Origin?.port u.uri_value.uri_origin)

(* Check if list in h is a sub-sequence of list in l *)
val origin_domain_match_sub : #s:secrecy_level -> list (secret_string s) -> list (secret_string s) -> Tot bool
let rec origin_domain_match_sub #s l h =
  match h with
  | [] -> true
  | hd::tl -> if hd = (classify_secret_string #PublicVal "*" s) then true
	    else 
	      match l with
	      | [] -> false
	      | hl::tll -> if hd = hl then origin_domain_match_sub tll tl
			 else false

(* Is path (cp) a prefix of the request-uri path (rp) *)
val pathMatch : #s:secrecy_level -> path s -> path s -> Tot bool
let pathMatch #s rp cp = origin_domain_match_sub rp cp

private val getPath : #s:secrecy_level -> u:uri{u.uri_secrecy_level = s} -> Tot (path s)
let getPath #s u = u.uri_value.uri_path

(* let blank_uri wid = URI ({sori=blank_origin;swid=wid}) ({uri_origin=blank_origin;uri_username="";uri_password=None;uri_path=[];uri_querystring=[];uri_fragment=""}) *)
let blank_uri = URI (PublicVal) ({uri_origin=blank_origin;uri_username="";uri_password="";uri_path=[];uri_querystring=[];uri_fragment=""})

(* Use this to get a URI indexed only by its origin - if it has pre-specified index, use the above function s*)
val hstring_to_uri : s:string -> Tot (option (uri))
let hstring_to_uri s = 
  match (hstring_to_curi_ml PublicVal s) with
  | None -> None
  | Some (o, x) -> 
      let os = (SecretVal [(SecOrigin o)]) in
      Some (URI os ({uri_origin=x.uri_origin;uri_username=classify_secret_string x.uri_username os;uri_password=classify_secret_string x.uri_password os;uri_path=classify_uri_path x.uri_path os;uri_querystring=classify_uri_querystring x.uri_querystring os;uri_fragment=classify_secret_string #PublicVal x.uri_fragment os}))
  
val getWinURI : cowindow -> Tot uri
let getWinURI w = w.cwin.cwloc

val getOriginURL : uri -> Tot uri
let getOriginURL u = 
  let nu = {uri_origin=u.uri_value.uri_origin;uri_username=empty_secret_string (u.uri_secrecy_level);uri_password=empty_secret_string (u.uri_secrecy_level);uri_path=[];uri_querystring=[];uri_fragment=empty_secret_string (u.uri_secrecy_level)} in
  URI (u.uri_secrecy_level) (nu)

(* referrer url with fragement and user, pwd set to null *)
val getRefURL : uri -> Tot uri
let getRefURL u = URI (u.uri_secrecy_level) ({u.uri_value with uri_username=empty_secret_string (u.uri_secrecy_level);uri_password=empty_secret_string (u.uri_secrecy_level);uri_fragment=empty_secret_string (u.uri_secrecy_level)})

val setUserPwd : #s:secrecy_level -> u:uri{u.uri_secrecy_level = s} -> secret_string s -> secret_string s -> Tot uri
let setUserPwd #s u user pd = URI (u.uri_secrecy_level) ({u.uri_value with uri_username=user;uri_password=pd})

(* Only set secure schemes - include as needed *)
(* in ({req with requrl=(list_replace_element_at req.requrl 1 nurl);reqref=refer;reqreferrer_policy=rP;corsflag=cors;recflag=rf})  *)

(* private val isValidURIRequest : uri -> GTot bool *)
(* let isValidURIRequest u = validSingleSecLevel (u.uri_secrecy_level) *)

private val setURIScheme : #bid:origin_opaque -> u:uri{is_origin_in_secrecy_level bid u.uri_secrecy_level} -> p:origin_protocol{p = "https"} -> 
			   Tot (nu:uri{is_origin_in_secrecy_level bid nu.uri_secrecy_level})
let setURIScheme #bid u p =
  let ou = u.uri_value in 
  let o = ou.uri_origin in
  let no = Origin p (Origin?.host o) (Origin?.port o) (Origin?.dom o) in
  let s = (match u.uri_secrecy_level with | PublicVal -> PublicVal | SecretVal s' -> (SecretVal ((SecOrigin no)::s'))) in 
  let nc = ({uri_origin=no;uri_username=reclassifyVal ou.uri_username s;uri_password=reclassifyVal ou.uri_password s;uri_path=recPath ou.uri_path s;uri_querystring=recQS ou.uri_querystring s;uri_fragment=reclassifyVal #(u.uri_secrecy_level) ou.uri_fragment s}) in
  URI s (mk_a_uri nc)

private val mk_stringHeader : #s:secrecy_level -> header_value' s -> Tot (secret_string s)
let mk_stringHeader #s hv = hv

private val reclassifySchemeHeader : h:header{checkHeaderSecLevel h} -> uri -> Tot (nh:header{checkHeaderSecLevel nh})
let rec reclassifySchemeHeader h u =
  let s = (u.uri_secrecy_level) in
  match h with
  | [] -> []
  | (f,v)::tl -> (match (v.hvs) with
		| PublicVal -> (reclassifySchemeHeader tl u)
		| SecretVal ol -> (f, Headervalue s (reclassifyVal (mk_stringHeader (v.hv)) s))::(reclassifySchemeHeader tl u))

val recSchemeHeaderLemma : h:header{checkHeaderSecLevel h} -> u:uri -> Lemma (requires (True)) 
		     (ensures (isHeaderVisible (reclassifySchemeHeader h u) (u.uri_secrecy_level)))
		     [SMTPat (reclassifySchemeHeader h u)]
let rec recSchemeHeaderLemma h u = match h with 
    | [] -> ()
    | hd::tl -> recSchemeHeaderLemma tl u

(* URL includes credentials if username is not empty or password is not null *)
val includesCredentials : uri -> Tot bool
let includesCredentials u = let sl = (u.uri_secrecy_level) in
  if (u.uri_value.uri_username <> empty_secret_string sl || u.uri_value.uri_password <> empty_secret_string sl) then true else false

val isSameAOrigin : a_origin -> a_origin -> Tot bool
let isSameAOrigin o0 o1 = is_same_origin o0 o1

val isSameOriginURI: uri -> uri -> Tot bool
let isSameOriginURI u0 u1 = is_same_origin u0.uri_value.uri_origin u1.uri_value.uri_origin

val isSameOriginUO: uri -> origin_tuple -> Tot bool
let isSameOriginUO u o = is_same_origin u.uri_value.uri_origin o

val isSameOriginWin: #cbid:origin_opaque -> cowindow' cbid -> cowindow' cbid  -> Tot bool
let isSameOriginWin #cbid cw_0 cw_1 = is_same_origin_domain (getOrigin cw_0.cwloc) (getOrigin cw_1.cwloc)
  
val isSameOriginDoc: a_document -> a_document -> Tot bool
let isSameOriginDoc d0 d1 = is_same_origin_domain d0.dloc.uri_value.uri_origin d1.dloc.uri_value.uri_origin

val mk_origin : a_origin -> Tot origin
let mk_origin ao = ao

val mk_aorigin : o:origin -> Tot a_origin
let mk_aorigin o = o

val setDocDomain : w:window -> origin_domain -> Tot (nw:window{nw.wbid = w.wbid})
let setDocDomain w h = 
  match (mk_origin w.w.wdoc.dori) with
  | Origin s h p d ->
      (
      let ori = Origin s h p (Some h) in
      let d = w.w.wdoc in
      let loc = setDomOrigin d.dloc (mk_aorigin ori) in
      Window w.wbid ({w.w with wdoc={d with dloc=loc;dori=ori};wloc=(loc)})
      )
  | OpaqueOrigin o -> w
  
private val uri_to_hstring : #s:secrecy_level -> u:uri{u.uri_secrecy_level = s} -> Tot (secret_string s)
let uri_to_hstring #s u = (uri_to_secret_string (u_curi u))

(* Implemented in ExtractURI as an ML function *)
private val hstring_to_curi : l:secrecy_level -> s:string -> Tot (option (origin_tuple * a_uri l))
let hstring_to_curi l s = hstring_to_curi_ml l s

val secstring_to_uri: #l:secrecy_level -> secret_string l -> Tot (option (u:uri{(u.uri_secrecy_level) = l}))
let secstring_to_uri #l s =
  match (hstring_to_curi l (declassify_secret_string s)) with
  | None -> None
  | Some (o, u) -> Some (URI l u) 
      




(* *** DOCUMENT *** *)
val getDocFlag : a_document -> sandbox_flags -> Tot bool
let getDocFlag d sbf =
  if (List.tryFind (fun w -> w = sbf) d.dsbox <> None) then true
  else false

val getRefPolicy : a_document -> Tot referrer_policy
let getRefPolicy d = d.drefPol

val getSBox : a_document -> Tot (list sandbox_flags)
let getSBox d = d.dsbox

val getDocOrigin : a_document -> Tot (origin)
let getDocOrigin d = d.dori

val is_opaqueDoc : a_document -> Tot bool
let is_opaqueDoc d = OpaqueOrigin? d.dori

val is_opaqueWin : cowindow -> Tot bool
let is_opaqueWin cw = is_opaqueDoc cw.cwin.cwdoc

val is_opaqueReq : browserRequest -> Tot bool
let is_opaqueReq req = OpaqueOrigin? (req.browser_request).reqo

val mk_adoc : document -> Tot a_document
let mk_adoc d = d

val getEffectiveDomain : document -> Tot (option origin_domain)
let getEffectiveDomain d =
  if (OpaqueOrigin? d.dori) then None 
  else match (Origin?.dom d.dori) with
      | None -> Some (Origin?.host d.dori)
      | Some dom -> Some dom

val getWinBID : #cbid:origin_opaque -> cowindow' cbid -> Tot origin_opaque
let getWinBID #cbid cw = cbid





(* *** SECURITY *** *)
(* Check if a particular window(p) is the parent (or ancestor) of the window(w)  *)
val isparentOrAncestor : #cbid:origin_opaque -> p:cowindow' cbid -> w:cowindow' cbid  -> Tot bool
let rec isparentOrAncestor #cbid p w =
  match w.cwparent with
  | None -> false
  | Some parent -> parent.cwinid = p.cwinid || (isparentOrAncestor p parent)

(* Check if a window/window's parent or ancestor is of the same origin as the given window(cw)*)
val isSameOriginAncestor: #cbid:origin_opaque -> cowindow' cbid -> cowindow' cbid  -> Tot bool
let rec isSameOriginAncestor #cbid cw w =
  if isSameOriginWin cw w then true
  else
    match w.cwparent with
    | None -> false
    | Some wp -> isSameOriginAncestor cw wp

(* HTML5 Spec 5.1.4 - Security *)
(* A familiar with B *)
val familiar_with: #cbid:origin_opaque -> cowindow' cbid -> cowindow' cbid  -> Tot bool
let rec familiar_with #cbid a b =
  if isSameOriginWin a b then true
  else if isparentOrAncestor a b then true
  else if isSameOriginAncestor a b then true
  else match b.cwopener with
       | None -> false
       | Some x -> familiar_with a x

(* A is allowed to navigate B *)
val allowed_navigation: #cbid:origin_opaque -> cowindow' cbid -> cowindow' cbid  -> Tot bool
let allowed_navigation #cbid a b =
  if a <> b && (isparentOrAncestor b a = false) &&
    b.cwparent <> None && (List.tryFind (fun w -> w = SB_Navigation) a.cwdoc.dsbox <> None) then false
  else if b.cwparent = None && (isparentOrAncestor a b)
    && (List.tryFind (fun w -> w = SB_TopWindow) a.cwdoc.dsbox <> None) then false
  else if b.cwparent = None && b <> a && (isparentOrAncestor a b = false) &&
    (List.tryFind (fun w -> w = SB_Navigation) a.cwdoc.dsbox <> None) then false (*Leaving out permitted sandboxed navigator*)
  else true

(* List of accessible windows from the current window in the browser *)
(* Additionally, it can access its frames and their frames *)
val accessible_windows : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> cowindow' cbid -> list (cowindow' cbid)  -> Tot (list (nw:cowindow' cbid))
let rec accessible_windows #cbid b w lw =
  match lw with
  | [] -> []
  | hw::tl -> if familiar_with w hw then hw::(accessible_windows b w tl)
	    else (accessible_windows b w tl)





(* *** WINDOW *** *)
(* Context-window functions *)
val win_to_cowin :  w:window -> Tot (cw:cowindow{w.wbid = cw.cwbid})
let win_to_cowin w = CWindow w.wbid ({cwinid=w.w.winid; cwname=w.w.wname; cwloc=w.w.wloc; cwframes=w.w.wframes; cwopener=w.w.wopener; cwparent=w.w.wparent; cwhist=w.w.whist; cwdoc=w.w.wdoc; cwsbox=w.w.wsbox})

val cowin_to_win : cw:cowindow -> Tot (w:window{w.wbid = cw.cwbid})
let cowin_to_win w = 
   Window w.cwbid ({winid=w.cwin.cwinid;wname=w.cwin.cwname;wloc=w.cwin.cwloc;wframes=w.cwin.cwframes;wopener=w.cwin.cwopener;wparent=w.cwin.cwparent;whist=w.cwin.cwhist;wdoc=w.cwin.cwdoc;wsbox=w.cwin.cwsbox})

val get_win_by_id_list : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> list (cowindow' cbid) -> wid -> Tot (option (cowindow' cbid))
let rec get_win_by_id_list #cbid b lw w = 
  match lw with
  | [] -> None
  | hd::tl -> if hd.cwinid = w then Some hd
	    else 
	      match (get_win_by_id_list b hd.cwframes w) with 
	      | None -> get_win_by_id_list b tl w
	      | Some x -> Some x 

val get_win_by_id : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> (cowindow' cbid) -> wid -> Tot (option (cowindow' cbid))
let get_win_by_id #cbid b cw w = get_win_by_id_list b cw.cwframes w

(* window.top *)
val get_top_window : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> (cowindow' cbid) -> Tot (cowindow' cbid)
let rec get_top_window #cbid b w =
  match w.cwparent with
  | None -> w
  | Some wp -> get_top_window b wp

val getFrames : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> (cowindow' cbid) -> Tot (list (cowindow' cbid)) 
let getFrames #cbid b w = w.cwframes

val getCSPList : cowindow -> Tot csp_policy
let getCSPList sw = sw.cwin.cwdoc.dCSP

(* Return the window given the window name in context of a current window(w) *)
val get_window_name : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> cowindow' cbid -> list (cowindow' cbid) -> n:string -> Tot (option (cowindow' cbid))
let rec get_window_name #cbid b w lc n =
  match lc with
  | [] -> None
  | wn::tl -> if (wn.cwname = n && familiar_with #cbid w wn) then Some wn
	    else match get_window_name b w (getFrames b wn) n with
		| None -> get_window_name b w tl n
		| Some win -> Some win

(* removes window from list and returns the modified list *)
val closewin : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> list (cowindow' cbid) -> cowindow' cbid ->  Tot (list (cowindow' cbid)) 
let rec closewin #cbid b wl w =
    match wl with
    | [] -> []
    | hd::tl -> if w.cwinid = hd.cwinid then tl
	      else hd::(closewin b tl w)

(* replaces the current window w with the new window tw *)
val replacewin : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> wl:list (cowindow' cbid) -> w:cowindow' cbid -> tw:cowindow' cbid{w.cwinid = tw.cwinid} -> 
		 Tot (l:list (cowindow' cbid){List.length wl = List.length l}) 
let rec replacewin #cbid b wl w tw =
    match wl with
    | [] -> []
    | hd::tl -> if w.cwinid = hd.cwinid then tw::tl
	      else hd::(replacewin b tl w tw)





(* *** HISTORY *** *)
(* (\* Get session histories *\) *)
(* val getSessionHistory : h:list historyEntry -> w:cowindow -> Tot (sh:(list sHistoryEntry){List.length sh = List.length h}) *)
(* let rec getSessionHistory lh w = *)
(*   match lh with *)
(*   | [] -> [] *)
(*   | h::tl -> {hsurl=h.heurl;hstime=h.hetime;hswin=w}::(getSessionHistory tl w) *)

(* val lemma_list_rep : l:list historyEntry -> n:nat -> w:wid -> e:historyEntry ->  *)
(* 	       Lemma (requires (forall x. List.mem x l ==> x.hewin = w) /\ (e.hewin = w))  *)
(* 		     (ensures (forall x. List.mem x (list_replace_element_at l n e) ==> x.hewin = w)) *)
(* let lemma_list_rep l n w e = list_replace_lemma l n e *)

(* Save the current document for the target window in history*)
val save_cur_doc_win : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> tw:cowindow' cbid -> Tot (w:cowindow' cbid{w.cwinid = tw.cwinid}) 
let save_cur_doc_win #cbid b tw =
  let u = tw.cwloc in 
  let he = HistEntry (u.uri_secrecy_level) u.uri_value get_time tw.cwdoc tw.cwinid in
  let nc = tw.cwhist.hcur in
  let nl = (list_replace_element_at tw.cwhist.hlhe nc he) in
  let nh = {hlhe=nl; hcur=nc} in (* (lemma_list_rep w.cwhist.hlhe nc w.cwinid he); *)
  ({cwinid=tw.cwinid; cwname=tw.cwname; cwloc=tw.cwloc; cwframes=tw.cwframes; cwopener=tw.cwopener; cwparent=tw.cwparent; cwhist=nh; cwdoc=tw.cwdoc; cwsbox=tw.cwsbox}) 

(* val lemma_list_app : l:list historyEntry -> l':list historyEntry -> w:wid ->  *)
(* 		     Lemma (requires ((forall x. List.mem x l ==> x.hewin = w) /\ (forall x. List.mem x l' ==> x.hewin = w))) *)
(* 		     (ensures (forall x. List.mem x (List.append l l') ==> x.hewin = w)) *)
(* let rec lemma_list_app l l' w =  *)
(*   match l with  *)
(*   | [] -> (match l' with *)
(* 	 | [] -> () *)
(* 	 | hd::tl -> lemma_list_app [] tl w) *)
(*   | hd::tl -> lemma_list_app tl l' w *)

(* Add new document to history *)
val add_doc_hist : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> tw:cowindow' cbid -> d:a_document -> Tot (cowindow' cbid)
let add_doc_hist #cbid b tw d =
  let he = HistEntry d.dloc.uri_secrecy_level d.dloc.uri_value get_time d tw.cwinid in
  let nc = (tw.cwhist.hcur + 1) in
  let rl = (list_remove_sublist tw.cwhist.hlhe tw.cwhist.hcur) in
  let nl = List.append rl [he] in
  let nh = {hlhe=nl; hcur=nc} in 
  list_append_lemma rl [he]; rem_list_sublist_lemma tw.cwhist.hlhe tw.cwhist.hcur;
  (* lemma_list_app rl [he] tw.cwinid; *)
  ({cwinid=tw.cwinid; cwname=tw.cwname; cwloc=d.dloc; cwframes=[]; cwopener=tw.cwopener; cwparent=tw.cwparent; cwhist=nh; cwdoc=d; cwsbox=tw.cwsbox})

(* Load the nth window in tw's history {nth <= List.length tw.whist.hl && nth > 0} *)
val load_nth_window : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> tw:cowindow' cbid -> delta:int -> Tot (cowindow' cbid * nb:browser{nb.bid = cbid})
let load_nth_window #cbid sb tw delta =
  let cp = (tw.cwhist.hcur + delta) in
  if (cp <= List.length tw.cwhist.hlhe && cp > 0) then
    let entry = (list_element_at tw.cwhist.hlhe (cp)) in
    let hist = ({tw.cwhist with hcur=cp}) in
    let s = entry.hsl in (* hist_lem entry; win_hist (CWin?.wsl tw) w entry cp; *) 
    let cw = ({cwinid=tw.cwinid; cwname=tw.cwname; cwloc=(URI entry.hsl entry.heurl); cwframes=tw.cwframes; cwopener=tw.cwopener; cwparent=tw.cwparent; cwhist=hist; cwdoc=entry.hedoc; cwsbox=tw.cwsbox}) in
    let tb = Browser (sb.bid) ({sb.br with windows=(replacewin sb sb.br.windows tw cw)}) in
    (cw, tb)
  else (tw, sb)

(* Quicksort impl from List.Tot for history sorting *)
private val partitionHist : nat -> list historyEntry -> Tot (list historyEntry * list historyEntry)
let rec partitionHist n l = 
  match l with 
  | [] -> [], []
  | hd::tl -> let l1, l2 = partitionHist n tl in
	    if n <= hd.hetime then hd::l1, l2
	    else l1, hd::l2

val partition_length_lemma: n:nat -> l:list historyEntry -> Lemma (requires True) (ensures (let (f,s) = (partitionHist n l) in List.length (f) + List.length (s) = List.length l)) 
						[SMTPat (partitionHist n l)]
let rec partition_length_lemma n l = match l with
  | [] -> ()
  | hd::tl -> partition_length_lemma n tl
  
(* Sort the history based on the time *)
private val sortHist : l:list historyEntry -> Tot (list historyEntry) (decreases (List.length l))
let rec sortHist l =
  match l with
  | [] -> []
  | pivot::tl -> 
      let (hi, lo) = partitionHist pivot.hetime tl in
      partition_length_lemma pivot.hetime tl;
      List.append (sortHist lo) (pivot::(sortHist hi))

(* **** For now assuming that the window has a joint history only *)  (* {List.length nl = List.length l} *)
(* Create a joint history from the frames' session history *)
private val joint_hist_frames : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> lf:list (cowindow' cbid) -> che:historyEntry -> Tot ((list historyEntry) * historyEntry)
let rec joint_hist_frames #cbid b lf che =
  match lf with
  | [] -> ([], che)
  | h::t -> let chist = h.cwhist in
	  if (chist.hcur = 0) then
	    let (fhl, fe) = (joint_hist_frames b (getFrames b h) che) in
	    let (nhl, ne) = (joint_hist_frames b t fe) in
	    (List.append chist.hlhe (List.append fhl nhl), ne)
	  else
	    let entry = (List.index chist.hlhe (chist.hcur - 1)) in
	    let jhist = list_remove_element_at chist.hlhe chist.hcur in
	    if (entry.hetime > che.hetime) then
	      let (fhl, fe) = (joint_hist_frames b (getFrames b h) entry) in
	      let (nhl, ne) = (joint_hist_frames b t fe) in
	      (List.append jhist (List.append fhl nhl), ne)
	    else
	      let (fhl, fe) = (joint_hist_frames b (getFrames b h) che) in
	      let (nhl, ne) = (joint_hist_frames b t fe) in
	      (List.append jhist (List.append fhl nhl), ne)

(* Create a joint history of the window and its frames *)
private val create_joint_history : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> (cowindow' cbid) -> Tot (list historyEntry * option historyEntry)
let create_joint_history #cbid b w =
  let whist = w.cwhist in
  if (whist.hcur = 0) then (* implies no history and no document *)
    ([], None)
  else
    let entry = (List.index whist.hlhe (whist.hcur - 1)) in
    let nhist = list_remove_element_at whist.hlhe whist.hcur in
    let (fhist, ce) = joint_hist_frames b (getFrames b w) entry in
    if (entry.hetime >= ce.hetime) then
      let nhl = sortHist(entry::(List.append nhist fhist)) in
      (nhl, Some entry)
    else
      let nhl = sortHist(ce::(List.append nhist fhist)) in
      (nhl, Some ce)
      (* let p = (list_element_position ce nhl 0) in *)
      (* 	if p <= List.length nhl then {hlhe=nhl; hcur=p} *)
      (* 	else {hlhe=nhl; hcur=0} (\* Case should not arise -- prove a property about this*\) *)

(* Save the current document for the target window in history*)
val save_cur_doc : #cbid:origin_opaque -> b:browser{b.bid = cbid} -> tw:cowindow' cbid -> Tot browser
let save_cur_doc #cbid b tw =
  let nw = (save_cur_doc_win b tw) in
  Browser b.bid ({b.br with windows=(replacewin b b.br.windows tw nw)})

#reset-options "--z3rlimit 100"

(* Take the tw window forward by one *)
val forward_history : #cbid:origin_opaque ->  b:browser{b.bid = cbid} -> cw:cowindow' cbid -> tw:(cowindow' cbid){isSameOriginWin cw tw} -> Tot (nb:browser{nb.bid = cbid})
let forward_history #cbid b cw tw =
    let top = (get_top_window b tw) in
    let (hist, he) = create_joint_history b top in
    match he with 
    | None -> (b)
    | Some che -> 
      let p = (list_element_position che hist 0) in
      if ((p+1) > List.length hist) then (b)
      else 
	let cur = (List.index hist p) in
	match (get_win_by_id b top cur.hewin) with
	| None -> (b) (* this should not arise, as the window in question should be present *)
	| Some cwin ->
	  let sb = (save_cur_doc b cwin) in
	  let (win, nb) = (load_nth_window sb cwin 1) in (* load the document in the window "win" *)
	  (nb)

(* Take the tw window back by one *)
val back_history : #cbid:origin_opaque ->  b:browser{b.bid = cbid} -> cw:cowindow' cbid -> tw:(cowindow' cbid){isSameOriginWin cw tw} -> Tot (nb:browser{nb.bid = cbid})
let back_history #cbid b cw tw =
    let top = (get_top_window b tw) in
    let (hist, he) = create_joint_history b top in
    match he with 
    | None -> (b)
    | Some che -> 
      let p = (list_element_position che hist 0) in
      if (p <= 0 || p > List.length hist) then (b)
      else 
	let cur = (List.index hist (p-1)) in
	match (get_win_by_id b top cur.hewin) with
	| None -> (b) 
	| Some cwin -> 
	  let sb = (save_cur_doc b cwin) in
	  let (win, nb) = (load_nth_window sb cwin (-1)) in (* load the document in the window "win" *)
	  (nb)





(* *** LOCALSTORAGE *** *)
(* LocalStorage auxiliary functions *)
val contains_entry_LSMap : b:browser -> list (e:localStorageEntry{b.bid = e.lsb}) -> origin_tuple -> Tot bool
let rec contains_entry_LSMap b l o = 
  match l with 
  | [] -> false
  | hd::tl -> (match hd with 
	    | LocalStorageEntry lb s e -> if s = o then true else contains_entry_LSMap b tl o)

val getLSEntry : b:browser -> list (e:localStorageEntry{b.bid = e.lsb}) -> o:origin_tuple -> 
		 Tot (dictionary #(secret_string (SecretVal [(SecOrigin o)])) #(secret_string (SecretVal [(SecOrigin o)])))
let rec getLSEntry b l o =
  match l with 
  | [] -> []
  | hd::tl -> (match hd with 
	    | LocalStorageEntry _ s e -> if s = o then e else getLSEntry b tl o)

val removeLSEntry : b:browser -> list (e:localStorageEntry{b.bid = e.lsb}) -> origin_tuple -> Tot (list (fe:localStorageEntry{b.bid = fe.lsb}))
let rec removeLSEntry b l o =
  match l with
  | [] -> l
  | hd::tl -> if (hd.ls_origin = o) then tl else hd::(removeLSEntry b tl o)

val updateLSMap : b:browser -> list (e:localStorageEntry{b.bid = e.lsb}) -> o:origin_tuple -> 
		  (dictionary #(secret_string (SecretVal [(SecOrigin o)])) #(secret_string (SecretVal [(SecOrigin o)]))) -> 
		  Tot (list (fe:localStorageEntry{b.bid = fe.lsb}))
let updateLSMap b l o d =
  let lsentry = (LocalStorageEntry b.bid o d) in
  if contains_entry_LSMap b l o then 
    lsentry::(removeLSEntry b l o)
  else 
    lsentry::l

val isSecureHost : browser -> uri -> Tot bool
let isSecureHost b u = is_origin_domain_in_list (Origin?.host u.uri_value.uri_origin) b.br.sts





(* *** CONNECTION *** *)
(* send request over one of the connections, and wait for response *)
(* Section 5.6 of RFC 7230 - response on a connection is sent to the first outstanding/pending request on that connection *)
val sendRequest : b:browser -> r:browserRequest{r.browser_request.reqbrowser = b.bid} -> bool -> (sw:cowindow{sw.cwbid = b.bid} * tw:cowindow{tw.cwbid = b.bid} * navType) -> 
		  Tot (result * nb:browser{nb.bid = b.bid /\ r.browser_request.reqbrowser = nb.bid})
let sendRequest b r cflag einfo =
  let c = {cori=getOrigin (List.hd r.browser_request.requrl); ccred=cflag} in
  let (sw, tw, ty) = einfo in
  match (List.tryFind (fun {connect=x;creq=rl} -> x.cori=c.cori && x.ccred = c.ccred) b.br.conn) with
  | None -> (Success ("LOG: request sent to " ^ (uri_to_string (List.hd r.browser_request.requrl)) ^ "\n"), 
		    Browser b.bid ({b.br with conn=({connect=c;creq=[(r, sw, tw, ty)]}::b.br.conn)}))
  | Some {connect=oconn;creq=oreq} ->
	let ncl = (({connect=oconn;creq=(List.append oreq [(r, sw, tw, ty)])})::(list_remove_element b.br.conn ({connect=oconn;creq=oreq}))) in
	(Success ("LOG: request sent to " ^ (uri_to_string (List.hd r.browser_request.requrl)) ^ "\n"), Browser b.bid ({b.br with conn=ncl}))

val getConnection : browser -> connection' -> Tot (option (connReq'))
let getConnection b c = 
  match (List.tryFind (fun ({connect=x;creq=rl}) -> x=c) b.br.conn) with
  | None -> None
  | Some x -> Some x

(* get the new connection pool after removing the first request for the connection*)
(* val getResponseConn : connectionPool -> connection -> Tot (r:(option (browserRequest * cowindow * cowindow * navType)) * f:(option bool) * connectionPool) *)
(* let getResponseConn cl c = *)
(*   match (List.tryFind (fun ({connect=x;creq=rl}) -> x = c) cl) with *)
(*   | None -> (None, None, cl) *)
(*   | Some c ->  *)
(*       (match c.creq with *)
(* 	| [] -> (None, Some c.connect.ccred, cl) *)
(* 	| (req)::tr -> (Some req, Some c.connect.ccred, (({connect=c.connect;creq=tr})::(list_remove_element cl c)))) *)

val getResponseConn : connectionPool -> connection -> Tot (option ((browserRequest * cowindow * cowindow * navType) * bool * connectionPool))
let getResponseConn cl c =
  match (List.tryFind (fun ({connect=x;creq=rl}) -> x = c) cl) with
  | None -> None
  | Some c -> 
      (match c.creq with
	| [] -> None
	| (req)::tr -> Some (req, c.connect.ccred, (({connect=c.connect;creq=tr})::(list_remove_element cl c))))

 
(* val option_response_conn_lemma : cl:connectionPool -> c:connection -> Lemma (requires (True))  *)
(* 			       (ensures (match (getResponseConn cl c) with | Some r, None, _ -> false | _, _, _ -> true)) [SMTPat (getResponseConn cl c)] *)
(* let option_response_conn_lemma cl c = () *)

val mk_connection : connection' -> Tot connection
let mk_connection c = c

val mk_conn : connection -> Tot connection'
let mk_conn c = c

val getConn : connReq -> Tot connReq'
let getConn c = c

val getConnReq : connReq' -> Tot (option browserRequest)
let getConnReq c =
  match c.creq with
  | [] -> None
  | (h,_,_,_)::_ -> Some h


 


(* *** Header PARSING *** *)
(* open ExtFunctionsImpl --- Implemented the ML version. Check Extra folder for the OCaml implementation *)

(* Total version of parseSerialAll *)
private val parseSerial : #l:secrecy_level -> secret_string l -> Tot (list (secret_string l))
let parseSerial #l s = parseSerialAll s

(* from serialized value retrieve the directive name/value*)
val getDirectiveFromString : string -> Tot (option csp_directive)
let getDirectiveFromString s = getDirectiveFromStringAll s

(* from serialized value retrieve the cookie name/value and attributes*)
(* getCookieFromStringAll returns cookie_header' *)
val getCookieFromString : l:secrecy_level{l <> PublicVal} -> secret_string l -> Tot (option (cookie_header (SecretVal?.sec_origin_list l)))
let getCookieFromString l s =
    match getCookieFromStringAll (SecretVal?.sec_origin_list l) (declassify_secret_string s) with
    | None -> None
    | Some c -> Some c

val emptyHeaderVal : header_value -> Tot bool
let emptyHeaderVal h = (h.hv = empty_secret_string (h.hvs))

val mk_headerval : #s:secrecy_level -> secret_string s -> Tot (header_value)
let mk_headerval #s t = Headervalue s t

(* Check if the request url is in the secrecy_level of the URI (or) should we add the origin to the secrecy_level *)
(* {match (u.uri_secrecy_level) with | PublicVal -> true | SecretVal sec -> List.mem (getOrigin (List.hd r.browser_request.requrl)) sec} *)
val getHeaderValueURI : r:browserRequest -> u:uri -> Tot (h:header_value) 
let getHeaderValueURI r u = 
  let s = r.breq_secrecy_level in
  let str = declassify_secret_string (uri_to_hstring #(u.uri_secrecy_level) u) in
  Headervalue s (reclassifyVal #PublicVal str s) (* need to reclassify_secret_string the header value for the URI that will receive it *)

val getHeaderValueOrigin : r:browserRequest -> Tot (h:header_value)
let getHeaderValueOrigin r =
  let s = r.breq_secrecy_level in
  if (Origin? (mk_origin r.browser_request.reqo)) then Headervalue s (classify_secret_string #PublicVal (origin_to_string r.browser_request.reqo) s)
  else Headervalue s (empty_secret_string s)

val parseCookieHeaderVal : #s:secrecy_level -> h:header_value{h.hvs = s} -> Tot (list (secret_string s))
let parseCookieHeaderVal #s h = parseSerialCookie (h.hv)

val parseHeaderVal : #s:secrecy_level -> h:header_value{h.hvs = s} -> Tot (list (secret_string s))
let parseHeaderVal #s h = parseSerial (h.hv)

val parseLocHeaderVal : #s:secrecy_level -> h:header_value{h.hvs = s} -> Tot (secret_string s)
let parseLocHeaderVal #s h = (h.hv)

(* Check the ABNF to determine how many header field values are allowed for each header *)
(* For multiple values, we assume that the list of origin is empty {List.find (fun (f,v) -> f = hf) h <> None} *) 
(* Also, assume that there are no duplicate field-names (they are probably combined before parsing) *)
private val parseHeader : h:header -> header_field -> Tot (option header_value)
let rec parseHeader h hf = 
  match h with
  | [] -> None
  | (f,v)::tl -> if (f=hf) then (Some v)
	       else (parseHeader tl hf)
	       
(* get cookie header from list string*)
private val getCookieFromHeaderList : #s:secrecy_level{s <> PublicVal} -> list (secret_string s) -> Tot (list (cookie_header (SecretVal?.sec_origin_list s)))
let rec getCookieFromHeaderList #s ls =
  match ls with
  | [] -> []
  | h::t -> (match getCookieFromString s h with
	  | None -> (getCookieFromHeaderList t)
	  | Some c -> c::(getCookieFromHeaderList t))

(* get csp_policy from list string*)
private val getCSPDirectivesList : #s:secrecy_level -> list (secret_string s) -> Tot csp_policy
let rec getCSPDirectivesList #s ls =
  match ls with
  | [] -> []
  | h::t -> match getDirectiveFromString (declassify_secret_string h) with (* in ExtFunctions.fsti *)
	  | None -> (getCSPDirectivesList t)
	  | Some d -> d::(getCSPDirectivesList t)

(* Get all the headers' names that are not in the list of header names *)
private val getAllHeadersNotIn : #s:secrecy_level -> header -> list (secret_string s) -> Tot (list string)
let rec getAllHeadersNotIn #s h ls =
  match h with
  | [] -> []
  | (n,_)::tl -> if (List.tryFind (fun x -> is_secret_equal_public_string x n) ls = None) then n::(getAllHeadersNotIn tl ls)
	       else getAllHeadersNotIn tl ls

(* removing headers still keeps the request valid *)
val removeForbiddenHeaderLemma : h:header{checkHeaderSecLevel h} -> 
				 r:browserRequest{isHeaderVisible h r.breq_secrecy_level} -> 
				 Lemma (requires (True)) 
				 (ensures (isHeaderVisible (removeForbiddenHeaderfieldInHeader h) r.breq_secrecy_level))
let rec removeForbiddenHeaderLemma h r = match h with 
    | [] -> ()
    | hd::tl -> removeForbiddenHeaderLemma tl r

(* create a new request without the forbidden headers to be used mostly for redirect -- Only those headers are sent on the redirect *)
val request_without_forbidden_headers : r:browserRequest -> 
					Tot (nr:browserRequest{notForbiddenHeaderfieldInReqHeader nr.browser_request.reqhead}) 
let request_without_forbidden_headers r = 
  let req = r.browser_request in
  let nh = (removeForbiddenHeaderfieldInHeader req.reqhead) in 
  (removeForbiddenHeaderLemma req.reqhead r);
  BrowserRequest r.breq_secrecy_level ({req with reqhead=nh})

val reclassifyForbiddenLemma : h:header{checkHeaderSecLevel h} -> u:uri -> Lemma (requires (notForbiddenHeaderfieldInReqHeader h)) 
			       (ensures (notForbiddenHeaderfieldInReqHeader (reclassifySchemeHeader h u))) [SMTPat (reclassifySchemeHeader h u)]
let rec reclassifyForbiddenLemma h u = 
  match h with 
  | [] -> ()
  | (f,v)::tl -> reclassifyForbiddenLemma tl u

(* make the origin_protocol of the request https *)
val makeRequestHTTPS : r:browserRequest{notForbiddenHeaderfieldInReqHeader r.browser_request.reqhead} -> 
		       Tot (nr:browserRequest{notForbiddenHeaderfieldInReqHeader nr.browser_request.reqhead}) 
let makeRequestHTTPS r =
  let req = r.browser_request in
  let u = setURIScheme #req.reqbrowser (List.hd req.requrl) "https" in
  let h = reclassifySchemeHeader req.reqhead u in 
  BrowserRequest (u.uri_secrecy_level) ({req with requrl=[u];reqhead=h;reqbody=reclassifyVal req.reqbody (u.uri_secrecy_level)})

(* convert method to string *)
private val toStringMethod : reqMethod -> Tot string
let toStringMethod m = m





(* *** RESPONSE - Definition *** *)

val isRedirectResponse : nat -> Tot bool
let isRedirectResponse rc = (rc >= 300 && rc <= 399) 

val isRedirectBodyResponse : nat -> Tot bool
let isRedirectBodyResponse rc = (rc = 307 || rc = 308) 

type respuri =
| Failure
| URL of uri

(* private val uriSecLevel : respuri -> GTot bool *)
(* let uriSecLevel r =  *)
(*   match r with *)
(*   | Failure -> true *)
(*   | URL u -> validSingleSecLevel (u.uri_secrecy_level)  *)

// RFC 7231 for details of HTTP semantics
// Resp_code 3XX indicates that it is a redirection
// Redirect to another uri - 301, 302, 303, 307
// Redirect request method changes from POST to GET for 301, 302 but NOT for 307
// if resp_code is 200, the status is ok and header contains response data
// if resp_code is 302 (page found) but the origin of the request is not allowed access return error
// if resp_code is 404, page is not found and return error
// Current URL is the first url in respurl if it is not empty
type browserResponse' (s:secrecy_level) = {
  respbrowser:origin_opaque;
  resptype:responseType;
  respcode:nat;
  respurl:list uri;
  resphead:header;
  respbody:secret_string s;
  resptrail:header;
  respHTTPS:httpstate;
  respCSP:csp_policy;
  respCORS:list header_field;
  resploc:(option respuri);
  respRedSec:(option secrecy_level)
}

val isValidHeader : origin -> header -> GTot bool
let rec isValidHeader o h = 
  match h with 
  | [] -> true
  | (hf,hv)::tl -> is_origin_in_secrecy_level o hv.hvs && isValidHeader o tl

(* Refer to 4.4. URL parsing of url.spec.whatwg.org *)
(* TODO - Do parsing of serialized value with base value as first element in u *)
private val getLocURL : #s:secrecy_level -> secret_string s -> list uri -> Tot (option respuri)
let getLocURL #s l u = match secstring_to_uri l with | None -> Some Failure | Some v -> Some (URL v)

(* Check if the location header's secrecy_level is included in the response's secrecy_level *)
val getLocationURI : #s:secrecy_level -> resp:(browserResponse' s) -> Tot (option respuri)
let getLocationURI #s resp =
  let (hl) = parseHeader resp.resphead "Location" in
  match hl with
  | None -> None 
  | Some hv -> match parseHeaderVal #hv.hvs hv with
	      | [] -> None (* TODO - when location header is not present, should we set it to none? *)
	      | h::_ -> getLocURL h resp.respurl
	      
private val isValidLocResp : #s:secrecy_level -> resp:browserResponse' s -> GTot bool
let isValidLocResp #s resp = (getLocationURI resp = resp.resploc)

(* Use this function to check if the secLevel of the redirect uri is what was expected by the response server *)
(* Also check if the response is redirect having valid secrecy level *)
private val isValidRedirect : #s:secrecy_level -> resp:browserResponse' s -> GTot bool
let isValidRedirect #s resp = 
  match (getLocationURI resp), resp.respRedSec with
  | Some (URL u), Some redirect_secrecy -> u.uri_secrecy_level = redirect_secrecy
  | Some (URL u), None -> false
  | _, _ -> true

private val isValidCookieResp : #s:secrecy_level -> resp:browserResponse' s -> GTot bool
let isValidCookieResp #s resp =
  match (parseHeader resp.resphead "Set-Cookie") with
  | None -> true
  | Some v -> (v.hvs <> PublicVal) && (can_restrict_secrecy_level v.hvs s) && (is_origin_in_secrecy_level resp.respbrowser v.hvs)

(* A response to request is valid ---
   Check if the redirect response is valid and can be reclassified appropriately and
   Check if the resploc of response is valid (populated by browser using the location header)
*)
val is_valid_browser_response : #s:secrecy_level -> browserResponse' s -> GTot bool
let is_valid_browser_response #s r = (isHeaderVisible r.resphead s) && (is_origin_in_secrecy_level r.respbrowser s) && (isValidHeader r.respbrowser r.resphead) &&
				     (isValidRedirect #s r) && (isValidLocResp #s r) && (isValidCookieResp #s r)
    
type browserResponse =
| BrowserResponse : bresp_secrecy_level:secrecy_level -> b_response:browserResponse' bresp_secrecy_level{is_valid_browser_response b_response} -> browserResponse

type response =
| RespSuccess of public_string
| NetworkError of public_string
| BResponse of browserResponse



val origin_header_lemma : o:origin -> h:header -> hf:header_field -> Lemma (requires (isValidHeader o h)) 
				    (ensures (match (parseHeader h hf) with | None -> true | Some v -> is_origin_in_secrecy_level o v.hvs))
let rec origin_header_lemma o h hf = 
  match h with 
  | [] -> ()
  | hd::tl -> origin_header_lemma o tl hf

val checkLocationURISecLevel : resp:browserResponse -> GTot (bool)
let checkLocationURISecLevel resp =
  let (hl) = parseHeader (resp.b_response).resphead "Location" in
  match hl, (resp.b_response).respRedSec with
  | None, _ -> true
  | Some hv, Some rs -> hv.hvs = rs (* can_restrict_secrecy_level ?? *)
  | Some _, None -> false (* for a valid location header, enforce that the redirect_secrecy_level be specified *)

(* returns whether the redirect response (307/308) is valid or not -- 
   assume that all redirect responses with code 307/308 should have public requests *)
private val is_valid_redirect_response : req:browserRequest -> resp:browserResponse -> GTot bool
let is_valid_redirect_response req resp = 
  if isRedirectResponse (resp.b_response).respcode && (Some? resp.b_response.respRedSec)then 
    (checkLocationURISecLevel resp) &&
    (canReclHeader (redirectHeaders (req.browser_request).reqhead) (Some?.v resp.b_response.respRedSec)) &&
    (is_origin_in_secrecy_level resp.b_response.respbrowser (Some?.v resp.b_response.respRedSec)) &&
    (if isRedirectBodyResponse (resp.b_response).respcode then 
      can_reclassify_secret_string (req.browser_request).reqbody (Some?.v resp.b_response.respRedSec)
     else true)
  else (resp.b_response).resploc = None (* if it is not a redirect response, the resploc field should not be populated *)
  
val is_valid_browser_response_for_request : req:browserRequest -> resp:browserResponse -> GTot bool
let is_valid_browser_response_for_request req resp = (is_valid_redirect_response req resp) && (resp.b_response.respbrowser = req.browser_request.reqbrowser)

val is_valid_response_for_request : req:browserRequest -> resp:response -> GTot bool
let is_valid_response_for_request req res = 
  match res with 
  | BResponse resp -> is_valid_browser_response_for_request req resp
  | _ -> true
  
private val isValidRedReclURI : req:browserRequest -> resp:browserResponse -> GTot bool
let isValidRedReclURI req resp = 
  match resp.b_response.respRedSec with
  | None -> true (* no redirect secrecy level, so return true *)
  | Some red -> (canReclHeader (redirectHeaders (req.browser_request).reqhead) red)

(* If a response to request is valid then headers can be reclassified *)
val validRedLemma : req:browserRequest -> resp:browserResponse -> 
		    Lemma (requires (is_valid_browser_response_for_request req resp /\ isRedirectResponse (resp.b_response.respcode)))
			  (ensures (isValidRedReclURI req resp))
		    [SMTPat (is_valid_browser_response_for_request req resp)]
let validRedLemma req resp = ()

val reqRespLocLemma : req:browserRequest -> resp:browserResponse -> 
		      Lemma (requires (is_valid_browser_response_for_request req resp /\ isRedirectResponse (resp.b_response.respcode))) 
			    (ensures (match (resp.b_response).resploc with | None -> true | Some Failure -> true 
				     | Some (URL u) -> (canReclHeader (redirectHeaders (req.browser_request).reqhead) (u.uri_secrecy_level))))
		      [SMTPat (is_valid_browser_response_for_request req resp)]
let reqRespLocLemma req resp = ()

(* If a response to request is valid then headers can be reclassified *)
val validCookieRespLemma : req:browserRequest -> resp:browserResponse -> 
		    Lemma (requires (is_valid_browser_response_for_request req resp))
			  (ensures (isValidRedReclURI req resp))
		    [SMTPat (is_valid_browser_response_for_request req resp)]
let validCookieRespLemma req resp = ()
  
type resource (b:browser) =
| RequestResource : req:browserRequest{notForbiddenHeaderfieldInReqHeader (req.browser_request).reqhead /\ req.browser_request.reqbrowser = b.bid} -> resource b
		    (*For urls, use default_request using the current window and url*)
| ResponseResource : req:browserRequest{req.browser_request.reqbrowser = b.bid} -> resp:response{is_valid_response_for_request req resp} -> resource b

val default_browser_request : b:browser -> w:cowindow{w.cwbid = b.bid} -> u:uri{is_origin_in_secrecy_level b.bid u.uri_secrecy_level} -> Tot (browserRequest)
let default_browser_request b w u = BrowserRequest (u.uri_secrecy_level) ({reqbrowser = b.bid; reqm = "GET"; requrl = [(u)]; reqhead = []; reqo = (getOrigin w.cwin.cwloc); reqw = (Some w); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client w); reqreferrer_policy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (empty_secret_string (u.uri_secrecy_level)); corsflag = false; corspfflag = false; authflag = false; recflag = false})





(* COOKIES *)
(* Unable to equate cookies as they can have different secrecy levels based on chost flag *)
private val get_old_cookie : #s:(secrecy_level){s <> PublicVal} -> b:browser -> (c_cookie s) -> 
			     (list (cs:cookie{is_origin_in_secrecy_level b.bid cs.cookie_secrecy_level})) -> 
			     Tot (option (c:cookie{is_origin_in_secrecy_level b.bid c.cookie_secrecy_level}))
let rec get_old_cookie #s b c cs =
  match cs with
  | [] -> None
  | ch::ct -> if (declassify_secret_string ch.c.cookie_name = declassify_secret_string c.cookie_name &&
		ch.c.cookie_domain = c.cookie_domain && 
		declassify_list_secret_string ch.c.cookie_path = declassify_list_secret_string c.cookie_path) then Some ch
	    else get_old_cookie b c ct

val httpOnly : cookie -> Tot bool
let httpOnly c = (Cookie?.c c).cookie_http_only

val createTime : cookie -> Tot string
let createTime c = (Cookie?.c c).cookie_create_time

(* Set cookie for the origin and replace only if similar cookie is present for that origin *)
private val set_cookie_in_store : b:browser -> c:cookie{is_origin_in_secrecy_level b.bid c.cookie_secrecy_level} -> 
				  (option (rc:cookie{is_origin_in_secrecy_level b.bid rc.cookie_secrecy_level})) -> 
				  Tot (nb:browser{nb.bid = b.bid})
let set_cookie_in_store b c rc =
  match rc with
  | Some oc -> Browser b.bid ({b.br with cookieStore=(c::(list_remove_element b.br.cookieStore oc))}) (* replace old with new. TODO - set new's creation to old *)
  | None -> Browser b.bid ({b.br with cookieStore=(c::b.br.cookieStore)})

(* opaque origins cannot access cookies? *)
val origin_access_cookie : #s:secrecy_level -> o:origin_tuple -> c:c_cookie s -> Tot (b:bool{b ==> can_origin_access_cookie o c})
let origin_access_cookie #s o c = 
  match o with 
  | Origin s h p d -> if c.cookie_host_only then h = c.cookie_domain else (origin_domain_match h c.cookie_domain)

(* Return only visible cookie list based on origin *)
private val get_cookies_from_store : s:secrecy_level -> u:uri{can_restrict_secrecy_level u.uri_secrecy_level s} -> list cookie -> 
				     Tot (list (c:cookie{can_restrict_secrecy_level c.cookie_secrecy_level s}))
let rec get_cookies_from_store s u lc =
  match lc with
  | [] -> []
  | c::tlc -> let cs = c.cookie_secrecy_level in 
	    if (origin_access_cookie (getOrigin u) c.c) && (SecretVal? s) && (SecretVal? cs) && 
	       (is_secrecy_origin_list_sublist (SecretVal?.sec_origin_list s) (SecretVal?.sec_origin_list cs)) then c::(get_cookies_from_store s u tlc)
	    else (get_cookies_from_store s u tlc)

(* Get current time for setting certain cookie attributes *)
(* Probably, not required unless clearing cookies *)
val curtime : string
let curtime = "1234" (* string_of_int (get_cur_time) *)

(* Take the domain cookie attribute and a request uri and return the appropriate cookie domain along with the host-only flag *)
(* 4.1.2.3 - RFC 6265 *)
private val get_cdomain_val : l:secrecy_level{l <> PublicVal} -> list cookie_header_attributes -> u:uri -> 
			      Tot (option (bool * h:origin_domain{origin_domain_match (Origin?.host (getOrigin u)) h /\ 
						  is_origin_domain_in_list_secrecy_origins h (SecretVal?.sec_origin_list l)}))
let get_cdomain_val l ca u =
  let da = List.tryFind (fun a -> match a with | CookieDomain _ -> true | _ -> false) ca in
  let h = (Origin?.host (getOrigin u)) in 
  match da with 
  | Some (CookieDomain cd) -> 
      if (List.length cd > 1 && origin_domain_match h cd && is_origin_domain_in_list_secrecy_origins cd (SecretVal?.sec_origin_list l)) then 
	 Some (false, cd)
      else None
  | None -> if (List.length h > 1) && origin_domain_match h h && is_origin_domain_in_list_secrecy_origins h (SecretVal?.sec_origin_list l) then 
	   Some (true, h)
	   else None
  | _ -> None

(* retrieve the expires/max-age attribute from the cookie header*)
private val get_cexpires_val : list cookie_header_attributes -> Tot (bool * string)
let get_cexpires_val ca =
  let ma = List.tryFind (fun a -> match a with | Max_age _ -> true | _ -> false) ca in
  match ma with
  | Some (Max_age m) -> (true, m)
  | None -> (let ea = List.tryFind (fun a -> match a with | Expires _ -> true | _ -> false) ca in
	   match ea with 
	   | Some (Expires e) -> (true, e)
	   | None -> (false, curtime)
	   | _ -> (false, curtime)) (* cases should not arise *)
  | _ -> (false, curtime)
  
(* Get the cookie's path value from the path attribute *)
private val get_cpath_val : #s:secrecy_level{s <> PublicVal} -> list cookie_header_attributes -> u:uri -> Tot (path s)
let get_cpath_val #s ca u =
  let pa = List.tryFind (fun a -> match a with | CookiePath _ -> true | _ -> false) ca in
  match pa with
  | Some (CookiePath cp) -> mk_list_secret_string #s cp
  | None -> recPath #(u.uri_secrecy_level) (getPath u) s
  | _ -> []

(* Get the cookie's secure-only value from the secureonly attribute *)
private val get_csecure_val : list cookie_header_attributes -> Tot bool
let get_csecure_val ca =
  let sa = List.tryFind (fun a -> match a with | SecureOnly -> true | _ -> false) ca in
  match sa with
  | Some (SecureOnly) -> true
  | None -> false
  | _ -> false

(* Get the cookie's http-only value from the httponly attribute *)
private val get_chttp_val : list cookie_header_attributes -> Tot bool
let get_chttp_val ca =
  let ha = List.tryFind (fun a -> match a with | HttpOnly -> true | _ -> false) ca in
  match ha with
  | Some (HttpOnly) -> true
  | None -> false
  | _ -> false

(* private val getSubDomains : h:origin_domain{match h with | [] -> false | _::tl -> not (list_is_empty tl)} -> o:origin{Origin? o} -> Tot (t:(list origin){not (list_is_empty t)}) *)
(* let rec getSubDomains h o = *)
(*   match h with *)
(*   | hd::tl -> if list_is_single_element_list tl then [(Origin (Origin?.protocol o) h (Origin?.port o) (Origin?.dom o))] *)
(* 	    else (Origin (Origin?.protocol o) h (Origin?.port o) (Origin?.dom o))::(getSubDomains tl o) (\* Do not include top-level domain *\) *)

(* private val getCookieOrigins : bool -> hd:origin_domain{match hd with | [] -> false | _::tl -> not (list_is_empty tl)} -> o:origin{Origin? o /\ origin_domain_match (Origin?.host o) hd} ->  *)
(* 			       Tot (t:(list origin){not (list_is_empty t)}) *)
(* let getCookieOrigins ho hd o =  *)
(*   let h = (Origin (Origin?.protocol o) hd (Origin?.port o) (Origin?.dom o)) in *)
(*   if ho then [h] else (getSubDomains hd o) *)

val cookie_access_origin_lemma : #s:secrecy_level{s <> PublicVal} -> c:c_cookie s -> nc:c_cookie s -> lo:list secrecy_origin ->
				 Lemma (requires (can_list_secrecy_origin_access_cookie lo c /\ 
						 c.cookie_name = nc.cookie_name /\ c.cookie_value = nc.cookie_value /\ 
						 c.cookie_domain = nc.cookie_domain /\ c.cookie_path = nc.cookie_path /\ c.cookie_host_only = nc.cookie_host_only)) 
				 (ensures (can_list_secrecy_origin_access_cookie lo nc)) 
let rec cookie_access_origin_lemma #s c nc lo = 
  match lo with 
  | [] -> ()
  | hd::tl -> cookie_access_origin_lemma c nc tl

private val setCookieAux : b:browser -> u:uri -> c:cookie{is_origin_in_secrecy_level b.bid c.cookie_secrecy_level} -> 
			   nhapi:bool -> Tot (nb:browser{nb.bid = b.bid})
let setCookieAux b u c nhapi = 
	if (c.c.cookie_http_only = true && (nhapi = true || ((getScheme u) <> "http" && (getScheme u) <> "https")))
	  then b (* cookie had http-only set but not received from http(s) origin_protocol or non-HTTP API; ignore *)
        else
          let cp = get_old_cookie b c.c b.br.cookieStore in
	  match cp with 
	  | None -> set_cookie_in_store b c (None)
	  | Some oc -> 
	      if (c.c.cookie_http_only = false && (httpOnly oc)) then b (* old cookie was http-only and new is not; ignore *)
	      else let nc = ({c.c with cookie_create_time=(createTime oc)}) in
		   cookie_access_origin_lemma c.c nc (SecretVal?.sec_origin_list c.cookie_secrecy_level);
		   set_cookie_in_store b (Cookie c.cookie_secrecy_level (mk_acookie nc)) (Some oc) 
	  | _ -> b (* shows a patterns are incomplete error!!! *)

private val can_access_cookie : #s:secrecy_level -> secrecy_origin -> c_cookie s -> Tot bool
let can_access_cookie #s o c = 
  match o with 
  | SecOrigin so -> (match so with 
		   | Origin sc h p d -> if c.cookie_host_only then h = c.cookie_domain else (origin_domain_match h c.cookie_domain)
		   | OpaqueOrigin op -> is_origin_in_secrecy_level so s)
  | OriginStar h -> if c.cookie_host_only then h = c.cookie_domain else (origin_domain_match h c.cookie_domain)

private val can_list_access_cookie : #s:secrecy_level -> lo:list secrecy_origin -> c:c_cookie s -> Tot (b:bool{b = can_list_secrecy_origin_access_cookie lo c})
let rec can_list_access_cookie #s lo c = 
  match lo with 
  | [] -> true
  | hd::tl -> can_access_cookie hd c && can_list_access_cookie tl c
			 
(* Section 5.3 of RFC6265 *)
(* Use the last set values - reverse the list when checking. List.tryFind returns the first found element? *)    
(* sets the cookie details in the browser's cookie store *)
(* u is the uri from which the cookie was received *)
(* nhapi indicates if the set-cookie is called from a non-HTTP API -> true indicates a non-HTTP API *)
private val set_cookie : b:browser -> s:secrecy_level{s <> PublicVal /\ is_origin_in_secrecy_level b.bid s} -> u:uri -> 
			 ch:(cookie_header (SecretVal?.sec_origin_list s)) -> nhapi:bool -> Tot (nb:browser{nb.bid = b.bid})
let set_cookie b s u ch nhapi = 
    let cattr = ch.cookie_header_attributes_list in
    let alist = List.rev cattr in 
    match (get_cdomain_val s alist u) with 
    | None -> b
    | Some (ho, hd) -> 
      let n = ch.cookie_header_name in
      let v = ch.cookie_header_value in
      let (pf, exp) = get_cexpires_val alist in 
      let c = ({cookie_name=n;cookie_value=v;cookie_expiry=exp;cookie_domain=hd;cookie_path=(get_cpath_val #s alist u);cookie_create_time=curtime;cookie_last_access=curtime;cookie_persistent=pf;cookie_host_only=ho;cookie_secure=(get_csecure_val alist);cookie_http_only=(get_chttp_val alist)}) in
      if can_list_access_cookie (SecretVal?.sec_origin_list s) c then 
	setCookieAux b u (Cookie s (mk_acookie c)) nhapi 
      else b
		   
(* Section 5.4 of RFC6265 *)
(* u is the uri to which the request is being sent *)
(* CookieStore should be sorted with longer paths before shorter paths when sending. If equal-secret_string_length then ebresp_secrecy_levelier creation time*)
(* Update the last-access time of the cookie in the store to current time -- Useful when removing cookies *)
private val get_cookies : s:secrecy_level -> u:uri{can_restrict_secrecy_level u.uri_secrecy_level s} -> 
			  list (c:(cookie){can_restrict_secrecy_level c.cookie_secrecy_level s}) -> nhapi:bool -> 
			  Tot (list (cs:cookie_send{cs.cs_secrecy_level = s}))
let rec get_cookies s u lc nhapi =
  let rh = (Origin?.host (getOrigin u)) in
  let prot = (Origin?.protocol (getOrigin u)) in
  match lc with
  | [] -> []
  | c::tl ->
    let hc = c.c in
    if ((recPath hc.cookie_path u.uri_secrecy_level) = (getPath u) || 
		 (pathMatch (getPath u) (recPath hc.cookie_path u.uri_secrecy_level))) then (* request path path-matches cookie-path*)
       let cs = {cookie_send_name=classify_secret_string hc.cookie_name s; cookie_send_value=classify_secret_string hc.cookie_value s} in (* Need some lemma here?? *)
       (if (hc.cookie_secure = true && prot = "https") then (*using only https for now, should add other secure schemes*)
	 (if hc.cookie_http_only = true && nhapi = false && (prot = "https" || prot = "http") then (*httponly flag set and http(s) scheme*)
	     (CookieSend s cs)::(get_cookies s u tl nhapi)
	  else if hc.cookie_http_only = false then (CookieSend s cs)::(get_cookies s u tl nhapi) (*httponly flag not set*)
	  else (get_cookies s u tl nhapi)) (*httponly flag set but not http(s) origin_protocol or non-http API *)
	else if hc.cookie_secure = false then (*secureonly flag not set*)
	  (if hc.cookie_http_only = true && (prot = "https" || prot = "http") then (*httponly flag set and http(s) scheme*)
	      (CookieSend s cs)::(get_cookies s u tl nhapi)
	   else if hc.cookie_http_only = false then (CookieSend s cs)::(get_cookies s u tl nhapi) (*httponly flag not set*)
	   else (get_cookies s u tl nhapi)) (*httponly flag set but not http(s) scheme*)
	else (get_cookies s u tl nhapi)) (*secureonly flag set and non-secure scheme*)
    else (get_cookies s u tl nhapi) (* path does not match *)

private val serialize_string : s:secrecy_level -> list (c:cookie_send{c.cs_secrecy_level = s}) -> Tot (secret_string s)
let rec serialize_string s cl =
  match cl with
  | [] -> empty_secret_string s
  | (CookieSend _ ck)::tc -> let c = secret_string_strcat ck.cookie_send_name (secret_string_strcat (classify_secret_string #PublicVal "=" s) 
							 (secret_string_strcat ck.cookie_send_value (classify_secret_string #PublicVal ";" s))) in
			   secret_string_strcat (c) (serialize_string s tc)

(* Serialize the cookie list into string *)
private val serialize_cookie_list : s:secrecy_level -> list (c:cookie_send{c.cs_secrecy_level = s}) -> Tot (hv:header_value{hv.hvs = s})
let serialize_cookie_list s l = Headervalue s (serialize_string s l)

private val get_cookie_list_from_store : o:origin_opaque -> list (c:cookie{is_origin_in_secrecy_level o c.cookie_secrecy_level}) -> Tot (list cookie)
let rec get_cookie_list_from_store o l = 
  match l with 
  | [] -> []
  | hd::tl -> hd::(get_cookie_list_from_store o tl)

(* Get the cookie-list as a string*)
val get_cookie_list : b:browser -> r:browserRequest -> bool -> Tot (hv:header_value{hv.hvs = r.breq_secrecy_level})
let get_cookie_list b r nhapi =
  let u = List.hd r.browser_request.requrl in
  let cl = get_cookies r.breq_secrecy_level u (get_cookies_from_store r.breq_secrecy_level u (get_cookie_list_from_store b.bid b.br.cookieStore)) nhapi in
  serialize_cookie_list r.breq_secrecy_level cl

(* Set all the cookies in the cookie_header list from response based on set_cookie algorithm *)
private val set_cookie_browser_sub : b:browser -> s:secrecy_level{s <> PublicVal /\ is_origin_in_secrecy_level b.bid s} -> u:uri ->
				     lc:list (cookie_header (SecretVal?.sec_origin_list s)) -> Tot (nb:browser{nb.bid = b.bid}) (decreases (List.length lc))
let rec set_cookie_browser_sub b s u lc =
  match lc with
  | [] -> b
  | hd::tl -> let nb = (set_cookie b s u hd false) in
	    set_cookie_browser_sub nb s u tl

(* set the cookies in the browser from the response *)
val set_cookie_browser : b:browser -> req:browserRequest{req.browser_request.reqbrowser = b.bid} -> 
			 resp:browserResponse{b.bid = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> Tot browser
let set_cookie_browser b req resp =
  let u = (List.hd req.browser_request.requrl) in
  match (parseHeader resp.b_response.resphead "Set-Cookie") with
  | None -> b
  | Some v -> origin_header_lemma resp.b_response.respbrowser resp.b_response.resphead "Set-Cookie";
	     (let c = getCookieFromHeaderList #v.hvs (parseCookieHeaderVal #(v.hvs) v) in
	     set_cookie_browser_sub b (v.hvs) u c)





(* *** Response-header parsing *** *)
val getCSPDirectives : resp:browserResponse -> Tot csp_policy
let getCSPDirectives resp =
  let l = (parseHeader (resp.b_response).resphead "Content-Security-Policy") in
  (match l with | None -> [] | Some v -> getCSPDirectivesList #(v.hvs) (parseHeaderVal v))

(* Section 5.9 - CORS check *)
(* missing check for "null" -- not defined in the spec *)
val corsCheck : req:browserRequest -> resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> Tot bool
let corsCheck req resp =
  let nreq = (req.browser_request) in
  let l = parseHeader (resp.b_response).resphead "Access-Control-Allow-Origin" in
  match l with 
  | None -> false (* origin is null *)
  | Some v -> 
      let hvorigin = parseHeaderVal #(v.hvs) v in
      if (nreq.reqcredm <> "include" && is_secret_equal_public_string (List.hd hvorigin) "*") then true
      else if (list_is_single_element_list hvorigin && (not (is_secret_equal_public_string (List.hd hvorigin) (origin_to_string nreq.reqo)))) then false
      else if (nreq.reqcredm <> "include") then true
      else (
	let lc = parseHeader (resp.b_response).resphead "Access-Control-Allow-Credentials" in 
	match lc with 
	| None -> false
	| Some cv -> (
	    let cred = parseHeaderVal #(cv.hvs) cv in
	    if (list_is_single_element_list cred && List.hd cred = classify_secret_string #PublicVal "true" cv.hvs) then true else false))

private val corsOKResponse1 : req:browserRequest -> resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> 
			      Tot (option (nresp:browserResponse{req.browser_request.reqbrowser = nresp.b_response.respbrowser /\ is_valid_browser_response_for_request req nresp}))
let corsOKResponse1 req resp = 
  let nreq = (req.browser_request) in
  if (List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) then None
  else if (List.for_all (fun (n,_) -> is_cors_safelisted_request_header_field n) nreq.reqhead) = false then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

private val corsOKResponse2 : req:browserRequest -> 
			      resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> vh:header_value -> 
			      Tot (option (nresp:browserResponse{req.browser_request.reqbrowser = nresp.b_response.respbrowser /\ is_valid_browser_response_for_request req nresp}))
let corsOKResponse2 req resp vh = 
  let nreq = (req.browser_request) in
  let (hheaders) = parseHeaderVal #(vh.hvs) vh in 
  if (List.tryFind (fun x -> is_secret_equal_public_string x "*") hheaders <> None) && (nreq.reqcredm = "include") then None
  else if ((List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) && 
      (List.tryFind (fun x -> is_secret_equal_public_string x "Authorization") hheaders = None)) then None
  else if (List.for_all (fun n -> is_cors_safelisted_request_header_field n) (getAllHeadersNotIn nreq.reqhead hheaders) = false &&
      List.tryFind (fun x -> is_secret_equal_public_string x "*") hheaders = None) then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

private val corsOKResponse3 : #l:secrecy_level -> req:browserRequest -> 
			      resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> list (secret_string l) -> 
			      Tot (option (nresp:browserResponse{req.browser_request.reqbrowser = nresp.b_response.respbrowser /\ is_valid_browser_response_for_request req nresp}))
let corsOKResponse3 #l req resp hmethods = 
  let nreq = (req.browser_request) in
  if ((List.tryFind (fun x -> is_secret_equal_public_string x "*") hmethods <> None) && nreq.reqcredm = "include") then None
  else if ((List.tryFind (fun x -> is_secret_equal_public_string x (toStringMethod nreq.reqm)) hmethods = None) && 
      (List.tryFind (fun x -> is_secret_equal_public_string x "*") hmethods = None) && (nreq.reqm <> "GET") && (nreq.reqm <> "POST") && (nreq.reqm <> "HEAD")) then None
  else if (List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) then None
  else if (List.for_all (fun (n,_) -> is_cors_safelisted_request_header_field n) nreq.reqhead) = false then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

private val corsOKResponse4 : #l:secrecy_level -> req:browserRequest -> 
			      resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> 
			      header_value -> list (secret_string l) -> 			     
			      Tot (option (nresp:browserResponse{req.browser_request.reqbrowser = nresp.b_response.respbrowser /\ is_valid_browser_response_for_request req nresp}))
let corsOKResponse4 #l req resp vh hmethods = 
  let nreq = (req.browser_request) in
  let (hheaders) = parseHeaderVal #(vh.hvs) vh in 
  if ((List.tryFind (fun x -> is_secret_equal_public_string x "*") hmethods <> None || List.tryFind (fun x -> is_secret_equal_public_string x "*") hheaders <> None) && nreq.reqcredm = "include") then None
  else if ((List.tryFind (fun x -> is_secret_equal_public_string x (toStringMethod nreq.reqm)) hmethods = None) && (List.tryFind (fun x -> is_secret_equal_public_string x "*") hmethods = None) &&
	  (nreq.reqm <> "GET") && (nreq.reqm <> "POST") && (nreq.reqm <> "HEAD")) then None
  else if ((List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) && (List.tryFind (fun x -> is_secret_equal_public_string x "Authorization") hheaders = None)) then None
  else if (List.for_all (fun n -> is_cors_safelisted_request_header_field n) (getAllHeadersNotIn nreq.reqhead hheaders) = false && List.tryFind (fun x -> is_secret_equal_public_string x "*") hheaders = None) then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

(* Step 7 of Section 5.7 *)
val corsOKResponse : req:browserRequest -> resp:browserResponse{req.browser_request.reqbrowser = resp.b_response.respbrowser /\ is_valid_browser_response_for_request req resp} -> 
		     Tot (option (nresp:browserResponse{req.browser_request.reqbrowser = nresp.b_response.respbrowser /\ is_valid_browser_response_for_request req nresp}))
let corsOKResponse req resp =
  let nreq = (req.browser_request) in
  let lm = parseHeader (resp.b_response).resphead "Access-Control-Allow-Methods" in
  let lh = parseHeader (resp.b_response).resphead "Access-Control-Allow-Headers" in
  match lm with
  | None ->  
      let hmeth = if (nreq.reqpreflight) then [(toStringMethod nreq.reqm)] else [] in
      if ((List.tryFind (fun x -> x = (toStringMethod nreq.reqm)) hmeth = None) && (List.tryFind (fun x -> x = "*") hmeth = None) &&
	 (nreq.reqm <> "GET") && (nreq.reqm <> "POST") && ((req.browser_request).reqm <> "HEAD")) then None
      else 
      (
	match lh with
	| None -> corsOKResponse1 req resp     
	| Some vh -> corsOKResponse2 req resp vh
      )
  | Some vm -> let (hmethods) = parseHeaderVal #(vm.hvs) vm in 
	      match lh with
	      | None -> corsOKResponse3 req resp hmethods
	      | Some vh -> corsOKResponse4 req resp vh hmethods

(* fs returns the last valid policy token *)
private val getRefPolicyToken: #s:secrecy_level -> list (secret_string s) -> string -> Tot string
let rec getRefPolicyToken #s hp fs =
  match hp with
  | [] -> fs
  | hd::t ->
	 if (is_secret_equal_public_string hd "no-referrer") then getRefPolicyToken t "no-referrer"
	 else if (is_secret_equal_public_string hd "no-referrer-when-downgrade") then getRefPolicyToken t "no-referrer-when-downgrade"
	 else if (is_secret_equal_public_string hd "strict-origin") then getRefPolicyToken t "strict-origin"
	 else if (is_secret_equal_public_string hd "strict-origin-when-cross-origin") then getRefPolicyToken t "strict-origin-when-cross-origin"
	 else if (is_secret_equal_public_string hd "same-origin") then getRefPolicyToken t "same-origin"
	 else if (is_secret_equal_public_string hd "origin") then getRefPolicyToken t "origin"
	 else if (is_secret_equal_public_string hd "origin-when-cross-origin") then getRefPolicyToken t "origin-when-cross-origin"
	 else if (is_secret_equal_public_string hd "unsafe-url") then getRefPolicyToken t "unsafe-url"
	 else getRefPolicyToken t fs

(* Referrer Policy --- 8.1. parse a referrer policy from a Referrer-Policy header *)
val parse_response_referrer_policy : browserResponse -> Tot referrer_policy
let parse_response_referrer_policy resp =
  let (hrpl) = parseHeader (resp.b_response).resphead "Referrer-Policy" in (* ABNF : 1#policy-token - assuming # to mean at least 1? *)
  match hrpl with
  | None -> RP_EmptyPolicy
  | Some hv -> 
      let hrp = parseHeaderVal #(hv.hvs) hv in
      let pol = getRefPolicyToken hrp "" in
      if pol = "no-referrer" then RP_NoReferrer
      else if pol = "no-referrer-when-downgrade" then RP_NoRefWhenDowngrade
      else if pol = "strict-origin" then RP_StrictOrigin
      else if pol = "strict-origin-when-cross-origin" then RP_StrictWhenCO
      else if pol = "same-origin" then RP_SameOrigin
      else if pol = "origin" then RP_Origin
      else if pol = "origin-when-cross-origin" then RP_OriginWhenCO
      else if pol = "unsafe-url" then RP_UnsafeURL
      else RP_EmptyPolicy

val getExposeHeaders : browserResponse -> Tot (list (header_field))
let getExposeHeaders r = 
    let s = parseHeader r.b_response.resphead "Access-Control-Expose-Headers" in 
    match s with
    | None -> []
    | Some v -> declassify_list_secret_string (parseHeaderVal #(v.hvs) v) 
	       	   




(* *** CSP *** *)
private val origin_match_expr_source : origin_tuple -> csp_directive_value -> origin_tuple -> nat -> Tot bool
let origin_match_expr_source ro dv orig redir =
  match dv with
  | DV_Any -> if Origin?.protocol ro = "http" || Origin?.protocol ro = "https" || Origin?.protocol ro = Origin?.protocol orig then true else false
  | DV_Self -> if (orig = ro) || (Origin?.host orig = Origin?.host ro && (Origin?.protocol orig = "http" && Origin?.protocol ro = "https")) (* check for ports *) then true
	      else false
  | DV_Scheme p -> if p = Origin?.protocol ro || (p = "http" && Origin?.protocol ro = "https") then true else false
  | DV_Origin o -> if o.op_protocol <> Origin?.protocol ro && (not (o.op_protocol = "http" && Origin?.protocol ro = "https")) then false
		  else if o.op_protocol = "" && (Origin?.protocol orig <> Origin?.protocol ro) &&
		    (not (Origin?.protocol orig = "http" && Origin?.protocol ro = "https")) then false
		  else if (not (origin_domain_match o.op_host (Origin?.host ro))) then false
		  (* else if  --- check for ports here *)
		  else if (o.op_path <> [] && redir = 0) then false (* path is [] for origin *)
		  else true
  | _ -> false

val origin_match_expr_source_list : uri -> list csp_directive_value -> uri -> nat -> Tot bool
let rec origin_match_expr_source_list r ls origU redir =
  let ro = getOrigin r in
  let orig = getOrigin origU in
  if (OpaqueOrigin? ro) then false
  else
  match ls with
  | [] -> false
  | hd::tl -> if (origin_match_expr_source ro hd orig redir) then true (* if matches return matches else check other values *)
	    else origin_match_expr_source_list r tl origU redir

(* 6.6.1.5. Does url match source list in origin with redirect count? *)
(* It is not clear what happens with multiple csp_directive_values starting from 'none' or 'none' in between?
   Currently, it seems the desired behavior is to allow checks on other csp_directive_values
*)
(* Check for every expression in the csp_directive_value list
   redir is the redirection count
*)
private val uri_match_expr_source : uri -> csp_directive_value -> origin_tuple -> nat -> Tot bool
let uri_match_expr_source u dv orig redir =
  let ro = getOrigin u in
  match dv with
  | DV_Any -> if Origin?.protocol ro = "http" || Origin?.protocol ro = "https" || Origin?.protocol ro = Origin?.protocol orig then true else false
  | DV_Self -> if (orig = ro) || (Origin?.host orig = Origin?.host ro && (Origin?.protocol orig = "http" && Origin?.protocol ro = "https")) (* check for ports *) then true
	      else false
  | DV_Scheme p -> if p = Origin?.protocol ro || (p = "http" && Origin?.protocol ro = "https") then true else false
  | DV_Origin o -> if o.op_protocol <> Origin?.protocol ro && (not (o.op_protocol = "http" && Origin?.protocol ro = "https")) then false
		  else if o.op_protocol = "" && (Origin?.protocol orig <> Origin?.protocol ro) &&
		    (not (Origin?.protocol orig = "http" && Origin?.protocol ro = "https")) then false
		  else if (not (origin_domain_match o.op_host (Origin?.host ro))) then false
		  (* else if  --- check for ports here *)
		  else if (o.op_path <> [] && redir = 0) then
		      (if (o.op_exact_match_flag = true && getPath u <> (mk_list_secret_string #(u.uri_secrecy_level) o.op_path)) then false
		      else if (not (pathMatch (getPath u) (mk_list_secret_string #(u.uri_secrecy_level) o.op_path))) then false
		      else true)
		  else true
  | _ -> false

private val uri_match_expr_source_list : r:uri -> list csp_directive_value -> orig:origin_tuple -> nat -> Tot bool
let rec uri_match_expr_source_list r ls orig redir =
  match ls with
  | [] -> false
  | hd::tl -> if (uri_match_expr_source r hd orig redir) then true (* if matches return matches else check other values *)
	    else uri_match_expr_source_list r tl orig redir

(* 6.6.1.3. Does request match source list? *)
(* match the request url with the directive value given the request's origin and redirect count - CSP*)
val uri_match_source : lu:(list uri){not (list_is_empty lu)} -> list csp_directive_value -> orig:a_origin -> nat -> Tot bool
let uri_match_source lu ls orig redir =
  if (OpaqueOrigin? orig) then false
  else
  match lu with
  | u::_ ->
    match ls with
    | [] -> false
    | [DV_None] -> false
    | _ -> uri_match_expr_source_list u ls orig redir

(* 6.6.1.4. Does response to request match source list? *)
(* match the response url with the directive value given the request's origin and redirect count - CSP*)
val uri_match_resp_source : lu:list uri -> list csp_directive_value -> orig:a_origin -> nat -> Tot bool
let uri_match_resp_source lu ls orig redir =
  if (OpaqueOrigin? orig) then false
  else
  match lu with
  | [] -> false (* although this should not be possible, for sanity check *)
  | u::_ -> match ls with
	  | [] -> false
	  | [DV_None] -> false
	  | _ -> uri_match_expr_source_list u ls orig redir
	   




(* DECLASSIFIERS *)
private val getHeaderVal : #s:secrecy_level -> hv:header_value{(hv.hvs) = s} -> Tot (secret_string s)
let getHeaderVal #s hv = (hv.hv)

(* Server functions *)
private val parsereqHeader : h:header -> hf:header_field -> Tot (option header_value)
let rec parsereqHeader h hf = 
  match h with
  | [] -> None
  | (f,v)::tl -> if (f=hf) then (Some v)
	       else (parsereqHeader tl hf)

val s_getHeaderValueString : #s:secrecy_level -> h:header_value{h.hvs = s} -> Tot (secret_string s)
let s_getHeaderValueString #s h = getHeaderVal h

val s_getURI : #s:secrecy_level -> u:uri{u.uri_secrecy_level = s} -> Tot (c_uri s)
let s_getURI #s u = (u_curi u)

val s_getBReqHeaderValue : browserRequest -> header_field -> Tot (list string)
let s_getBReqHeaderValue req h =
  match (parsereqHeader (req.browser_request).reqhead h) with
  | None -> []
  | Some v -> let s = (if (h = "Cookie") then parseCookieHeaderVal #(v.hvs) v else parseHeaderVal #(v.hvs) v) in
	     declassify_list_secret_string s
  
(* val s_getRequestURI : #s:secrecy_level -> req:browserRequest{(URI?.uri_secrecy_level (List.hd (req.browser_request).requrl)) = s} -> Tot (c_uri s) *)
(* let s_getRequestURI #s req = u_curi (List.hd (req.browser_request).requrl) *)

val s_getBrowserRequestOrigin : browserRequest -> Tot origin
let s_getBrowserRequestOrigin req = (mk_origin (req.browser_request).reqo)

(* val s_getURISecLevel : #s:secrecy_level -> c_uri s -> Tot (l:secrecy_level{l = s}) *)
(* let s_getURISecLevel #s u = s *)

(* val s_getReqURISecLevel : browserRequest  -> Tot (l:secrecy_level) *)
(* let s_getReqURISecLevel req = (URI?.uri_secrecy_level (List.hd (req.browser_request).requrl)) *)

(* val s_getRequestBody : #s:secrecy_level -> req:browserRequest{req.breq_secrecy_level = s} -> Tot (secret_string s) *)
(* let s_getRequestBody #s req = (req.browser_request).reqbody *)

val s_secstring_uri: #l:secrecy_level -> secret_string l -> Tot (option (origin_tuple * a_uri l))
let s_secstring_uri #l s = (hstring_to_curi_ml l (declassify_secret_string s))  



(* Generic function for accessing the secrecy level of various datatypes *)
(* add all browser types *)
type browserTypes =
| BBrowserRequest 
| BBrowser
| BCookie

let browserVal (t:browserTypes) =
match t with 
| BBrowserRequest -> browserRequest 
| BBrowser -> browser
| BCookie -> cookie

let levelOf (#t:browserTypes) (v:browserVal t) = 
match t with
| BBrowserRequest -> v.breq_secrecy_level
| BBrowser -> PublicVal
| _ -> PublicVal 
