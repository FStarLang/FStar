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

abstract type a_origin = origin 
  
type document = {
  dloc:uri;
  dref:uri;
  dori:a_origin;
  dHTTPS:httpstate;
  drefPol:refPolicy;
  dCSP:csp_policy;
  dsbox:list sandboxFlags;
}

abstract type a_document = document

(* For now, every history entry contains the minimal information, i.e., the url of the page*)
(* It may also contain state, title, document, form-data, scroll-restoration, scroll position, name etc.*)
type historyEntry = 
| HistEntry : hsl:secLevel -> heurl:a_uri hsl -> hetime:nat -> hedoc:document -> hewin:wid -> historyEntry

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
| LocalStorageEntry : lsl:secLevel{lsl <> PublicVal && (List.length (SecretVal?.seco lsl) = 1)} -> ldict:dictionary -> localStorageEntry
type c_localStorageMap = list localStorageEntry

abstract type localStorageMap = c_localStorageMap 

type cowindow =
| CWindow : cwinid:wid -> cwname:pubString -> cwloc:uri -> cwframes:list (cowindow) -> cwopener:option (cowindow) -> cwparent:option (cowindow) -> cwhist:a_history{forall x. List.mem x (ahist_to_hist cwhist).hlhe ==> (HistEntry?.hewin x = cwinid)} -> cwdoc:a_document -> cwsbox:list sandboxFlags -> cowindow

(* (\* Needed for refinement *\) *)
(* type cowindow' (s:secLevel) :Type0 = *)
(* | CWindow : cwinid:wid -> cwname:pubString -> cwloc:a_uri s -> cwframes:list (cowindow) -> cwopener:option (cowindow) -> cwparent:option (cowindow) -> cwhist:a_history{forall x. List.mem x (ahist_to_hist cwhist).hlhe ==> (HistEntry?.hewin x = cwinid)} -> cwdoc:a_document -> cwsbox:list sandboxFlags -> cowindow' s *)
(* and cowindow = *)
(* | CWin : wsl:secLevel -> cw:(cowindow' wsl) -> cowindow *)

(* type cowindow =  *)
(* | CWin : wsl:secLevel -> cwinid:wid{wsl.swid = cwinid} -> cwname:a_string -> cwloc:a_uri wsl -> cwframes:list (cowindow) -> cwopener:option (cowindow) -> cwparent:option (cowindow) -> cwhist:a_history -> cwdoc:a_document{isSameOriginDom (Document.dsl cwdoc).sori (wsl.sori) /\ (Document.dsl cwdoc).swid=wsl.swid} -> cwsbox:list sandboxFlags -> cowindow *)
(* and cowindow = *)
(* | CWin : wsl:secLevel -> cw:(cowindow' wsl){(wsl.swid = (CWindow.cwinid cw) /\ isSameOriginDom (Doc.dsl (CWindow.cwdoc cw)).sori (wsl.sori) /\ (Doc.dsl (CWindow.cw c)).swid=wsl.swid)} -> cowindow *)

type window' = {
  winid:wid;
  wname:pubString;
  wloc:uri;
  wframes:list (cowindow);
  wopener:option (cowindow);
  wparent:option (cowindow);
  whist:history;
  wdoc:document;
  wsbox:list sandboxFlags;
}

(* all history entries should have the window id as the current window's id *)
(* type window = w:window'{ isSameOriginDom (Doc.dsl w.wdoc).sori (w.wloc.c_origin) /\   *)
type window = w:window'{(forall x. List.mem x w.whist.hlhe ==> (HistEntry?.hewin x = w.winid))}

(* Referer (sic) corresponding to referer header*)
type referer=
| NoReferrer
| Client of cowindow
| URLReferrer of uri 

(* A request can have a lot of associated fields as pointed out in 3.1.5 of Fetch spec (fetch.spec.whatwg.org). We model only few interesting ones here.
   Current URL is the first url in requrl
*)
type requestFormat (s:secLevel) = {
  reqm:reqMethod;
  requrl:list uri;
  reqhead:header;
  reqo:a_origin;
  reqw:option (cowindow);
  reqinit:initiator;
  reqtype:requesttype;
  reqdest:destination;
  reqtarget:option (cowindow);
  reqredirect:nat;
  reqredmode:redirectVal;
  reqref:referer;
  reqrefPolicy:refPolicy;
  reqnonce:pubString;
  reqparser:parserVal;
  requnsafe:bool;
  reqpreflight:bool;
  reqsync:bool;
  reqmode:mode;
  reqtaint:taintVal;
  reqcredm:credmode;
  reqcredflag:bool;
  reqbody:secString s;
  corsflag:bool;
  corspfflag:bool;
  authflag:bool;
  recflag:bool;
}

private val getOrigin : uri -> Tot torigin
let getOrigin u = (URI?.u u).c_origin

(* val uriReqSecLevel : s:secLevel -> uri -> GTot bool *)
(* let uriReqSecLevel s u = *)
(*   match s with  *)
(*   | PublicVal -> (URI?.usl u = PublicVal) *)
(*   | SecretVal [o] -> (match URI?.usl u with | PublicVal -> false | SecretVal ol -> isSublist [o] ol) *)
(*   | _ -> false *)

(* construct a valid request to be sent on the network *)
val isValidRequest : #s:secLevel -> rf:requestFormat s -> Tot bool
let isValidRequest #s rf = 
  if (emptyList rf.requrl) then false
  else 
    let u = (firstElement rf.requrl) in 
    match s with
    | PublicVal -> (URI?.usl u = s)
    | SecretVal ol -> (URI?.usl u = s) && (isHeaderVisible rf.reqhead ol)
    
val validRequestLemma : #s:secLevel -> rf:(requestFormat s){isValidRequest #s rf /\ checkHeaderSecLevel rf.reqhead} -> 
			Lemma (requires (True)) (ensures (s = URI?.usl (firstElement rf.requrl))) [SMTPat (isValidRequest #s rf)]
let validRequestLemma #s rf = ()

type request = 
| Request : (rsl:secLevel) -> rf:(requestFormat rsl){isValidRequest rf /\ checkHeaderSecLevel rf.reqhead} -> request

val default_request : cowindow -> u:uri -> Tot (request)
let default_request w u = Request (URI?.usl u) ({reqm = "GET"; requrl = [(u)]; reqhead = []; reqo = (getOrigin (CWindow?.cwloc w)); reqw = (Some w); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client w); reqrefPolicy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (emptyString (URI?.usl u)); corsflag = false; corspfflag = false; authflag = false; recflag = false})

(* Section 3.4 Fetch spec - Connections*)
type connection' = {
  cori:torigin;
  ccred:bool;
}

abstract type connection = connection'

type connReq' = {
  connect:connection;
  creq:list (request * cowindow * cowindow * navType); (* windows required for processing response *)
}

abstract type connReq = connReq'

type connectionPool = list connReq (*contains the list of pending requests for that connection*)

(* add STS for automatic upgrades of the requests to HTTPS *)
type browser :Type0 = {
  windows:list cowindow;
  cookieStore:list cookie;
  localStorage:localStorageMap;
  sts:list hdomain;
  conn:connectionPool;
  next_u_id:wid;
}





(* ***** INITIALIZE BROWSER ***** *)
let init_browser:browser = {windows=[];cookieStore=[];localStorage=[];sts=[];conn=[];next_u_id=1}

(* Generate unique ids *)
val set_unique_id : browser -> Tot (wid * browser)
let set_unique_id b = (b.next_u_id, {b with next_u_id=(b.next_u_id + 1)})

val set_op_origin : browser -> Tot (o:a_origin * browser)
let set_op_origin b = (OOrigin b.next_u_id, {b with next_u_id=(b.next_u_id + 1)})

(* val noWindow : a_document -> Tot bool *)
(* let noWindow d = (d.dwin = 0) *)

val noWin : wid
let noWin = 0

(* let blank_doc = Document blank_uri blank_uri "none" RP_EmptyPolicy [] 0 [] "" *)
(* let blank_doc b = {dloc=blank_uri;dref=blank_uri;dori=OOrigin (get_unique_id b);dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=[];dwin=0;dsbox=[]} *)




(* ***** Functions for abstraction ***** *)
(* *** URI *** *)
private val get_c_uri : #s:secLevel -> browser -> cowindow -> u:uri{URI?.usl u = s} -> Tot (option (c_uri s))
let get_c_uri #s b sw u =
  match u with
  | URI l loc -> if isSameOriginDom (getOrigin (CWindow?.cwloc sw)) loc.c_origin then Some loc else None

val get_win_curi : #s:secLevel -> browser -> cowindow -> tw:cowindow{(URI?.usl tw.cwloc = s)} -> Tot (option (c_uri s))
let get_win_curi #s b sw tw = get_c_uri b sw (tw.cwloc)

private val reclassifyVal : #l:secLevel -> s:secString l -> l':(secLevel) -> Tot (t:(secString l'){content t = content s})
let reclassifyVal #l s l' =
    match l,l' with
    | PublicVal,PublicVal -> s
    | PublicVal,SecretVal ol -> classify s l'	
    | SecretVal _,PublicVal -> declassify s
    | SecretVal ol,SecretVal ol' -> 
	(match s with | AString #ol s -> let a:a_string ol' = AString #ol' s in a)
	
(* Some private reclassify functions for URI's security level --- use reclassifyVal only here *) 
private val recPath : #s:secLevel -> path s -> s':secLevel -> Tot (path s')
let rec recPath #s l s' =
  match l with
  | [] -> []
  | hd::tl -> (reclassifyVal hd s')::(recPath tl s')

val classifyPath : #s:secLevel -> path s -> s':secLevel{restricts s s'} -> Tot (path s')
let classifyPath #s l s' =
  match l with
  | [] -> []
  | hd::tl -> (classify hd s')::(classifyPath tl s')

private val recQS : #s:secLevel -> querystring s -> s':secLevel -> Tot (querystring s')
let rec recQS #s l s' =
  match l with
  | [] -> []
  | (hq,hv)::tl -> (reclassifyVal hq s', reclassifyVal hv s')::(recQS tl s')

val classifyQS : #s:secLevel -> querystring s -> s':secLevel{restricts s s'} -> Tot (querystring s')
let rec classifyQS #s l s' =
  match l with
  | [] -> []
  | (hq,hv)::tl -> (classify hq s', classify hv s')::(classifyQS tl s')

private val u_curi : #s:secLevel -> u:uri{URI?.usl u = s} -> Tot (c_uri s)
let u_curi #s u = mk_curi (URI?.u u)

val equalAOrigin : a_origin -> a_origin -> Tot bool
let equalAOrigin a0 a1 = a0 = a1

(* val getFragmentString : fragment -> Tot string *)
(* let getFragmentString f = f *)

val emptyFragment : u:uri -> Tot bool
let emptyFragment u = eqString #(URI?.usl u) (URI?.u u).c_fragment ""

val getAOrigin : uri -> Tot a_origin
let getAOrigin u = (URI?.u u).c_origin

(* val setOrigin : uri -> torigin -> Tot uri *)
(* let setOrigin u o = URI (SecretVal [o]) (mk_auri #(SecretVal [o]) ({URI?.u u with c_origin = o})) *)

private val setDomOrigin : uri -> a_origin -> Tot uri
let setDomOrigin u o = 
  if (TOrigin? o) then 
    let os = (match (URI?.usl u) with
	     | PublicVal -> (SecretVal [o]) (* Should we keep it Public? *)
	     | SecretVal ol -> (SecretVal (o::ol))) in (* reclassify including the older origins - used in setDocumentDomain *)
    URI os ({c_origin=o;c_uname=reclassifyVal (URI?.u u).c_uname os;c_pwd=reclassifyVal (URI?.u u).c_pwd os;c_path=recPath (URI?.u u).c_path os;c_querystring=recQS (URI?.u u).c_querystring os;c_fragment=reclassifyVal #(URI?.usl u) (URI?.u u).c_fragment os})
  else u

val getScheme : uri -> Tot scheme
let getScheme u = (TOrigin?.protocol (URI?.u u).c_origin)

val getPort : uri -> Tot (option port)
let getPort u = (TOrigin?.port (URI?.u u).c_origin)

(* Check if list in h is a sub-sequence of list in l *)
val dMatch : #s:secLevel -> list (secString s) -> list (secString s) -> Tot bool
let rec dMatch #s l h =
  match h with
  | [] -> true
  | hd::tl -> if hd = (classify #PublicVal "*" s) then true
	    else 
	      match l with
	      | [] -> false
	      | hl::tll -> if hd = hl then dMatch tll tl
			 else false

(* Is path (cp) a prefix of the request-uri path (rp) *)
val pathMatch : #s:secLevel -> path s -> path s -> Tot bool
let pathMatch #s rp cp = dMatch rp cp

private val getPath : #s:secLevel -> u:uri{URI?.usl u = s} -> Tot (path s)
let getPath #s u = (URI?.u u).c_path

(* let blank_uri wid = URI ({sori=blank_origin;swid=wid}) ({c_origin=blank_origin;c_uname="";c_pwd=None;c_path=[];c_querystring=[];c_fragment=""}) *)
let blank_uri = URI (PublicVal) ({c_origin=blank_origin;c_uname="";c_pwd="";c_path=[];c_querystring=[];c_fragment=""})

(* Use this to get a URI indexed only by its origin - if it has pre-specified index, use the above function s*)
val hstring_to_uri : s:string -> Tot (option (uri))
let hstring_to_uri s = 
  match (hstring_to_curi_ml PublicVal s) with
  | None -> None
  | Some (o, x) -> 
      let os = (SecretVal [o]) in
      Some (URI os ({c_origin=x.c_origin;c_uname=classify x.c_uname os;c_pwd=classify x.c_pwd os;c_path=classifyPath x.c_path os;c_querystring=classifyQS x.c_querystring os;c_fragment=classify #PublicVal x.c_fragment os}))
  
val getWinURI : cowindow -> Tot uri
let getWinURI w = (CWindow?.cwloc w)

val getOriginURL : uri -> Tot uri
let getOriginURL u = 
  let nu = {c_origin=(URI?.u u).c_origin;c_uname=emptyString (URI?.usl u);c_pwd=emptyString (URI?.usl u);c_path=[];c_querystring=[];c_fragment=emptyString (URI?.usl u)} in
  URI (URI?.usl u) (nu)

(* referrer url with fragement and user, pwd set to null *)
val getRefURL : uri -> Tot uri
let getRefURL u = URI (URI?.usl u) ({(URI?.u u) with c_uname=emptyString (URI?.usl u);c_pwd=emptyString (URI?.usl u);c_fragment=emptyString (URI?.usl u)})

val setUserPwd : #s:secLevel -> u:uri{URI?.usl u = s} -> secString s -> secString s -> Tot uri
let setUserPwd #s u user pd = URI (URI?.usl u) ({(URI?.u u) with c_uname=user;c_pwd=pd})

(* Only set secure schemes - include as needed *)
(* in ({req with requrl=(replace_elem_list req.requrl 1 nurl);reqref=refer;reqrefPolicy=rP;corsflag=cors;recflag=rf})  *)

(* private val isValidURIRequest : uri -> GTot bool *)
(* let isValidURIRequest u = validSingleSecLevel (URI?.usl u) *)

private val setURIScheme : uri -> p:scheme{p = "https"} -> Tot (u:uri)
let setURIScheme u p =
  let ou = (URI?.u u) in 
  let o = ou.c_origin in
  let no = TOrigin p (TOrigin?.host o) (TOrigin?.port o) (TOrigin?.dom o) in
  let s = (match URI?.usl u with | PublicVal -> PublicVal | SecretVal s' -> (SecretVal (no::s'))) in 
  let nc = ({c_origin=no;c_uname=reclassifyVal ou.c_uname s;c_pwd=reclassifyVal ou.c_pwd s;c_path=recPath ou.c_path s;c_querystring=recQS ou.c_querystring s;c_fragment=reclassifyVal #(URI?.usl u) ou.c_fragment s}) in
  URI s (mk_auri nc)

private val mk_stringHeader : #s:secLevel -> headervalue' s -> Tot (secString s)
let mk_stringHeader #s hv = hv

private val reclassifySchemeHeader : h:header{checkHeaderSecLevel h} -> uri -> Tot (nh:header{checkHeaderSecLevel nh})
let rec reclassifySchemeHeader h u =
  let s = (URI?.usl u) in
  match h with
  | [] -> []
  | (f,v)::tl -> (match (Headervalue?.hvs v) with
		| PublicVal -> (reclassifySchemeHeader tl u)
		| SecretVal ol -> (f, Headervalue s (reclassifyVal (mk_stringHeader (Headervalue?.hv v)) s))::(reclassifySchemeHeader tl u))

val recSchemeHeaderLemma : h:header{checkHeaderSecLevel h} -> u:uri -> Lemma (requires (SecretVal? (URI?.usl u))) 
		     (ensures (match URI?.usl u with | SecretVal ol -> isHeaderVisible (reclassifySchemeHeader h u) ol | PublicVal -> true))
		     [SMTPat (reclassifySchemeHeader h u)]
let rec recSchemeHeaderLemma h u = match h with 
    | [] -> ()
    | hd::tl -> recSchemeHeaderLemma tl u

(* URL includes credentials if username is not empty or password is not null *)
val includesCredentials : uri -> Tot bool
let includesCredentials u = let sl = (URI?.usl u) in
  if ((URI?.u u).c_uname <> emptyString sl || (URI?.u u).c_pwd <> emptyString sl) then true else false

val isSameAOrigin : a_origin -> a_origin -> Tot bool
let isSameAOrigin o0 o1 = isSameOrigin o0 o1

val isSameOriginURI: uri -> uri -> Tot bool
let isSameOriginURI u0 u1 = isSameOrigin (URI?.u u0).c_origin (URI?.u u1).c_origin

val isSameOriginUO: uri -> origin -> Tot bool
let isSameOriginUO u o = isSameOrigin (URI?.u u).c_origin o

val isSameOriginWin: cw0:cowindow -> cw1:cowindow -> Tot bool
let isSameOriginWin cw0 cw1 = isSameOriginDom (getOrigin (CWindow?.cwloc cw0)) (getOrigin (CWindow?.cwloc cw1))
  
val isSameOriginDoc: a_document -> a_document -> Tot bool
let isSameOriginDoc d0 d1 = isSameOriginDom (URI?.u d0.dloc).c_origin (URI?.u d1.dloc).c_origin

val mk_origin : a_origin -> Tot origin
let mk_origin ao = ao

val mk_aorigin : origin -> Tot a_origin
let mk_aorigin o = o

val setDocDomain : w:window -> o:a_origin{TOrigin? (mk_origin o)} -> hdomain -> Tot (window)
let setDocDomain w o h = 
  let ori = TOrigin (TOrigin?.protocol o) (TOrigin?.host o) (TOrigin?.port o) (Some h) in
  let d = w.wdoc in
  let loc = setDomOrigin d.dloc ori in
  ({w with wdoc={d with dloc=loc;dori=o};wloc=(loc)})

private val uri_to_hstring : #s:secLevel -> u:uri{URI?.usl u = s} -> Tot (secString s)
let uri_to_hstring #s u = (curi_to_hstring (u_curi u))

(* Implemented in ExtractURI as an ML function *)
private val hstring_to_curi : l:secLevel -> s:string -> Tot (option (torigin * a_uri l))
let hstring_to_curi l s = hstring_to_curi_ml l s

val secstring_to_uri: #l:secLevel -> secString l -> Tot (option (u:uri{equalSubLevels (URI?.usl u) l}))
let secstring_to_uri #l s =
  match (hstring_to_curi l (declassify s)) with
  | None -> None
  | Some (o, u) -> Some (URI l u) 
      




(* *** DOCUMENT *** *)
val getDocFlag : a_document -> sandboxFlags -> Tot bool
let getDocFlag d sbf =
  if (List.tryFind (fun w -> w = sbf) d.dsbox <> None) then true
  else false

val getRefPolicy : a_document -> Tot refPolicy
let getRefPolicy d = d.drefPol

val getSBox : a_document -> Tot (list sandboxFlags)
let getSBox d = d.dsbox

val getDocOrigin : a_document -> Tot (origin)
let getDocOrigin d = d.dori

val is_opaqueDoc : a_document -> Tot bool
let is_opaqueDoc d = OOrigin? d.dori

val is_opaqueWin : cowindow -> Tot bool
let is_opaqueWin cw = is_opaqueDoc (CWindow?.cwdoc cw)

val is_opaqueReq : request -> Tot bool
let is_opaqueReq req = OOrigin? (Request?.rf req).reqo

val mk_adoc : document -> Tot a_document
let mk_adoc d = d

val getEffectiveDomain : document -> Tot (option hdomain)
let getEffectiveDomain d =
  if (OOrigin? d.dori) then None 
  else match (TOrigin?.dom d.dori) with
      | None -> Some (TOrigin?.host d.dori)
      | Some dom -> Some dom





(* *** SECURITY *** *)
(* Check if a particular window(p) is the parent (or ancestor) of the window(w)  *)
val isParentOrAncestor : p:cowindow -> w:cowindow  -> Tot bool
let rec isParentOrAncestor p w =
  match (CWindow?.cwparent w) with
  | None -> false
  | Some p_i -> ((CWindow?.cwinid p_i) = (CWindow?.cwinid p)) || (isParentOrAncestor p p_i)

(* Check if a window/window's parent or ancestor is of the same origin as the given window(cw)*)
val isSameOriginAncestor: cowindow -> cowindow -> Tot bool
let rec isSameOriginAncestor cw w =
  if isSameOriginWin cw w then true
  else
    match (CWindow?.cwparent w) with
    | None -> false
    | Some wp -> isSameOriginAncestor cw wp

(* HTML5 Spec 5.1.4 - Security *)
(* A familiar with B *)
val familiar_with: cowindow -> cowindow -> Tot bool
let rec familiar_with a b =
  if isSameOriginWin a b then true
  else if isParentOrAncestor a b then true
  else if isSameOriginAncestor a b then true
  else match (CWindow?.cwopener b) with
       | None -> false
       | Some x -> familiar_with a x

(* A is allowed to navigate B *)
val allowed_navigation: cowindow -> cowindow -> Tot bool
let allowed_navigation a b =
  if a <> b && (isParentOrAncestor b a = false) &&
    (CWindow?.cwparent b) <> None && (List.tryFind (fun w -> w = SB_Navigation) (CWindow?.cwdoc a).dsbox <> None) then false
  else if (CWindow?.cwparent b) = None && (isParentOrAncestor a b)
    && (List.tryFind (fun w -> w = SB_TopWindow) (CWindow?.cwdoc a).dsbox <> None) then false
  else if (CWindow?.cwparent b) = None && b <> a && (isParentOrAncestor a b = false) &&
    (List.tryFind (fun w -> w = SB_Navigation) (CWindow?.cwdoc a).dsbox <> None) then false (*Leaving out permitted sandboxed navigator*)
  else true

(* List of accessible windows from the current window in the browser *)
(* Additionally, it can access its frames and their frames *)
val accessible_windows : cowindow -> list cowindow -> Tot (list cowindow)
let rec accessible_windows w lw =
  match lw with
  | [] -> []
  | hw::tl -> if familiar_with w hw then hw::(accessible_windows w tl)
	    else (accessible_windows w tl)





(* *** WINDOW *** *)
(* Context-window functions *)
val win_to_cowin : window -> Tot cowindow
let win_to_cowin w = CWindow w.winid w.wname w.wloc w.wframes w.wopener w.wparent w.whist w.wdoc w.wsbox

val cowin_to_win : cowindow -> Tot (window)
let cowin_to_win w = 
    ({winid=(CWindow?.cwinid w);wname=(CWindow?.cwname w);wloc=(CWindow?.cwloc w);wframes=(CWindow?.cwframes w);wopener=(CWindow?.cwopener w);wparent=(CWindow?.cwparent w);whist=(CWindow?.cwhist w);wdoc=(CWindow?.cwdoc w);wsbox=(CWindow?.cwsbox w)})

val get_win_by_id_list : list cowindow -> wid -> Tot (option cowindow)
let rec get_win_by_id_list lw w = 
  match lw with
  | [] -> None
  | hd::tl -> if (CWindow?.cwinid hd) = w then Some hd
	    else 
	      match (get_win_by_id_list (CWindow?.cwframes hd) w) with 
	      | None -> get_win_by_id_list tl w
	      | Some x -> Some x 

val get_win_by_id : browser -> cowindow -> wid -> Tot (option cowindow)
let get_win_by_id b cw w = get_win_by_id_list (CWindow?.cwframes cw) w

(* window.top *)
val get_top_window : w:cowindow -> Tot cowindow
let rec get_top_window w =
  match (CWindow?.cwparent w) with
  | None -> w
  | Some wp -> get_top_window wp

val getFrames : cowindow -> Tot (list cowindow)
let getFrames w = (CWindow?.cwframes w)

val getCSPList : cowindow -> Tot csp_policy
let getCSPList sw = (CWindow?.cwdoc sw).dCSP

(* Return the window given the window name in context of a current window(w) *)
val get_window_name : w:cowindow -> lc:list cowindow -> n:string -> Tot (option cowindow)
let rec get_window_name w lc n =
  match lc with
  | [] -> None
  | wn::tl -> if ((CWindow?.cwname wn) = n && familiar_with w wn) then Some wn
	    else match get_window_name w (getFrames wn) n with
		| None -> get_window_name w tl n
		| Some win -> Some win

(* removes window from list and returns the modified list *)
val closewin : list cowindow -> cowindow -> Tot (list cowindow)
let rec closewin wl w =
    match wl with
    | [] -> []
    | hd::tl -> if (CWindow?.cwinid w) = (CWindow?.cwinid hd) then tl
	      else hd::(closewin tl w)

(* replaces the current window w with the new window tw *)
val replacewin : wl:list cowindow -> w:cowindow -> tw:cowindow{(CWindow?.cwinid w) = (CWindow?.cwinid tw)} -> Tot (l:list cowindow{List.length wl = List.length l})
let rec replacewin wl w tw =
    match wl with
    | [] -> []
    | hd::tl -> if (CWindow?.cwinid w) = (CWindow?.cwinid hd) then tw::tl
	      else hd::(replacewin tl w tw)





(* *** HISTORY *** *)
(* (\* Get session histories *\) *)
(* val getSessionHistory : h:list historyEntry -> w:cowindow -> Tot (sh:(list sHistoryEntry){List.length sh = List.length h}) *)
(* let rec getSessionHistory lh w = *)
(*   match lh with *)
(*   | [] -> [] *)
(*   | h::tl -> {hsurl=h.heurl;hstime=h.hetime;hswin=w}::(getSessionHistory tl w) *)

(* val lemma_list_rep : l:list historyEntry -> n:nat -> w:wid -> e:historyEntry ->  *)
(* 	       Lemma (requires (forall x. List.mem x l ==> HistEntry?.hewin x = w) /\ (HistEntry?.hewin e = w))  *)
(* 		     (ensures (forall x. List.mem x (replace_elem_list l n e) ==> HistEntry?.hewin x = w)) *)
(* let lemma_list_rep l n w e = replace_lemma l n e *)

(* Save the current document for the target window in history*)
val save_cur_doc_win : tw:cowindow -> Tot cowindow
let save_cur_doc_win tw =
  let u = (CWindow?.cwloc tw) in 
  let he = HistEntry (URI?.usl u) (URI?.u u) get_time (CWindow?.cwdoc tw) (CWindow?.cwinid tw) in
  let nc = ((CWindow?.cwhist tw).hcur) in
  let nl = (replace_elem_list (CWindow?.cwhist tw).hlhe nc he) in
  let nh = {hlhe=nl; hcur=nc} in (* (lemma_list_rep w.cwhist.hlhe nc w.cwinid he); *)
  (CWindow (CWindow?.cwinid tw) (CWindow?.cwname tw) (CWindow?.cwloc tw) (CWindow?.cwframes tw) (CWindow?.cwopener tw) (CWindow?.cwparent tw) nh (CWindow?.cwdoc tw) (CWindow?.cwsbox tw)) 

val lemma_list_app : l:list historyEntry -> l':list historyEntry -> w:wid -> 
		     Lemma (requires ((forall x. List.mem x l ==> HistEntry?.hewin x = w) /\ (forall x. List.mem x l' ==> HistEntry?.hewin x = w)))
		     (ensures (forall x. List.mem x (List.append l l') ==> HistEntry?.hewin x = w))
let rec lemma_list_app l l' w = 
  match l with 
  | [] -> (match l' with
	 | [] -> ()
	 | hd::tl -> lemma_list_app [] tl w)
  | hd::tl -> lemma_list_app tl l' w

(* Add new document to history *)
val add_doc_hist : tw:cowindow -> d:a_document -> Tot (cowindow)
let add_doc_hist tw d =
  let he = HistEntry (URI?.usl d.dloc) (URI?.u d.dloc) get_time d (CWindow?.cwinid tw) in
  let nc = ((CWindow?.cwhist tw).hcur + 1) in
  let rl = (rem_sublist (CWindow?.cwhist tw).hlhe (CWindow?.cwhist tw).hcur) in
  let nl = List.append rl [he] in
  let nh = {hlhe=nl; hcur=nc} in 
  lemma_list_append rl [he]; rem_sublist_lemma tw.cwhist.hlhe tw.cwhist.hcur;
  lemma_list_app rl [he] (CWindow?.cwinid tw);
  ((CWindow (CWindow?.cwinid tw) (CWindow?.cwname tw) d.dloc [] (CWindow?.cwopener tw) (CWindow?.cwparent tw) nh d (CWindow?.cwsbox tw)))

(* Load the nth window in tw's history {nth <= List.length tw.whist.hl && nth > 0} *)
val load_nth_window : sb:browser -> tw:cowindow -> delta:int -> Tot (cowindow * browser)
let load_nth_window sb tw delta =
  let cp = ((CWindow?.cwhist tw).hcur + delta) in
  if (cp <= List.length (CWindow?.cwhist tw).hlhe && cp > 0) then
    let entry = (eqIndex (CWindow?.cwhist tw).hlhe (cp)) in
    let hist = ({(CWindow?.cwhist tw) with hcur=cp}) in
    let s = ((HistEntry?.hsl entry)) in (* hist_lem entry; win_hist (CWin?.wsl tw) w entry cp; *) 
    let cw = (CWindow (CWindow?.cwinid tw) (CWindow?.cwname tw) (URI (HistEntry?.hsl entry) (HistEntry?.heurl entry)) (CWindow?.cwframes tw) (CWindow?.cwopener tw) (CWindow?.cwparent tw) hist (HistEntry?.hedoc entry) (CWindow?.cwsbox tw)) in
    let tb = ({sb with windows=(replacewin sb.windows tw cw)}) in
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

val partition_length: n:nat -> l:list historyEntry -> Lemma (requires True) (ensures (let (f,s) = (partitionHist n l) in List.length (f) + List.length (s) = List.length l)) 
						[SMTPat (partitionHist n l)]
let rec partition_length n l = match l with
  | [] -> ()
  | hd::tl -> partition_length n tl
  
(* Sort the history based on the time *)
private val sortHist : l:list historyEntry -> Tot (list historyEntry) (decreases (List.length l))
let rec sortHist l =
  match l with
  | [] -> []
  | pivot::tl -> 
      let hi, lo  = partitionHist pivot.hetime tl in
      (* partition_length pivot.hetime tl; *)
      List.append (sortHist lo) (pivot::(sortHist hi))

(* **** For now assuming that the window has a joint history only *)  (* {List.length nl = List.length l} *)
(* Create a joint history from the frames' session history *)
private val joint_hist_frames : lf:list cowindow -> che:historyEntry -> Tot ((list historyEntry) * historyEntry)
let rec joint_hist_frames lf che =
  match lf with
  | [] -> ([], che)
  | h::t -> let chist = (cowin_to_win h).whist in
	  if (chist.hcur = 0) then
	    let (fhl, fe) = (joint_hist_frames (getFrames h) che) in
	    let (nhl, ne) = (joint_hist_frames t fe) in
	    (List.append chist.hlhe (List.append fhl nhl), ne)
	  else
	    let entry = (List.index chist.hlhe (chist.hcur - 1)) in
	    let jhist = remove_elem_list_n chist.hlhe chist.hcur in
	    if (entry.hetime > che.hetime) then
	      let (fhl, fe) = (joint_hist_frames (getFrames h) entry) in
	      let (nhl, ne) = (joint_hist_frames t fe) in
	      (List.append jhist (List.append fhl nhl), ne)
	    else
	      let (fhl, fe) = (joint_hist_frames (getFrames h) che) in
	      let (nhl, ne) = (joint_hist_frames t fe) in
	      (List.append jhist (List.append fhl nhl), ne)

(* Create a joint history of the window and its frames *)
private val create_joint_history : w:cowindow -> Tot (list historyEntry * option historyEntry)
let create_joint_history w =
  let whist = (cowin_to_win w).whist in
  if (whist.hcur = 0) then (* implies no history and no document *)
    ([], None)
  else
    let entry = (List.index whist.hlhe (whist.hcur - 1)) in
    let nhist = remove_elem_list_n whist.hlhe whist.hcur in
    let (fhist, ce) = joint_hist_frames (getFrames w) entry in
    if (entry.hetime >= ce.hetime) then
      let nhl = sortHist(entry::(List.append nhist fhist)) in
      (nhl, Some entry)
    else
      let nhl = sortHist(ce::(List.append nhist fhist)) in
      (nhl, Some ce)
      (* let p = (pos ce nhl 0) in *)
      (* 	if p <= List.length nhl then {hlhe=nhl; hcur=p} *)
      (* 	else {hlhe=nhl; hcur=0} (\* Case should not arise -- prove a property about this*\) *)

(* Save the current document for the target window in history*)
val save_cur_doc : b:browser -> tw:cowindow -> Tot browser
let save_cur_doc b tw =
  let nw = (save_cur_doc_win tw) in
  {b with windows=(replacewin b.windows tw nw)}
  
(* Take the tw window forward by one *)
val forward_history : b:browser -> cw:cowindow -> tw:cowindow{isSameOriginWin cw tw} -> Tot (browser)
let forward_history b cw tw =
    let top = (get_top_window tw) in
    let (hist, he) = create_joint_history top in
    match he with 
    | None -> (b)
    | Some che -> 
      let p = (pos che hist 0) in
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
val back_history : b:browser -> cw:cowindow -> tw:cowindow{isSameOriginWin cw tw (* eqSecLevel (URI?.usl (CWindow?.cwloc cw)) (URI?.usl (CWindow?.cwloc tw)) *)} -> 
		   Tot (browser)
let back_history b cw tw =
    let top = (get_top_window tw) in
    let (hist, he) = create_joint_history top in
    match he with 
    | None -> (b)
    | Some che -> 
      let p = (pos che hist 0) in
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
val mk_alsmap : c_localStorageMap -> Tot localStorageMap
let mk_alsmap l = l

val containsLSMap : localStorageMap -> torigin -> Tot bool
let containsLSMap l o = (List.tryFind (fun e -> match (LocalStorageEntry?.lsl e) with | SecretVal [entry] -> entry = o) l <> None)

val getLSEntry : l:localStorageMap -> o:torigin -> Tot dictionary
let getLSEntry l o =
  match (List.tryFind (fun e -> match (LocalStorageEntry?.lsl e) with | SecretVal [entry] -> entry = o) l) with
  | Some e -> e.ldict
  | None -> []

val removeLSEntry : localStorageMap -> torigin -> Tot localStorageMap
let rec removeLSEntry l o =
  match l with
  | [] -> l
  | hd::tl -> if (match (LocalStorageEntry?.lsl hd) with | SecretVal [entry] -> entry = o) then tl else hd::(removeLSEntry tl o)

val updateLSMap : localStorageMap -> torigin -> dictionary -> Tot localStorageMap
let updateLSMap l o d =
  match (List.tryFind (fun e -> match (LocalStorageEntry?.lsl e) with | SecretVal [entry] -> entry = o) l) with
  | None -> (LocalStorageEntry (SecretVal [o]) d)::l
  | Some e -> (LocalStorageEntry (SecretVal [o]) d)::(removeLSEntry l o)
  (* match l with  *)
  (* | [] -> [(LocalStorageEntry (SecretVal [o]) d)] *)
  (* | hd::tl -> if (match (LocalStorageEntry?.lsl hd) with | SecretVal [entry] -> entry = o) then (LocalStorageEntry (SecretVal [o]) d)::(removeLSEntry l o)  *)
  (* 	    else hd::(updateLSMap tl o d) *)

val isSecureHost : browser -> uri -> Tot bool
let isSecureHost b u = hostMatch (TOrigin?.host (URI?.u u).c_origin) b.sts





(* *** CONNECTION *** *)
(* send request over one of the connections, and wait for response *)
(* Section 5.6 of RFC 7230 - response on a connection is sent to the first outstanding/pending request on that connection *)
val sendRequest : browser -> request -> bool -> (cowindow * cowindow * navType) -> Tot (result * browser)
let sendRequest b r cflag einfo =
  let c = {cori=getOrigin (firstElement (Request?.rf r).requrl); ccred=cflag} in
  let (sw, tw, ty) = einfo in
  match (List.tryFind (fun {connect=x;creq=rl} -> x.cori=c.cori && x.ccred = c.ccred) b.conn) with
  | None -> (Success ("LOG: request sent to " ^ (uri_to_hstring_val (firstElement (Request?.rf r).requrl)) ^ "\n"), {b with conn=({connect=c;creq=[(r, sw, tw, ty)]}::b.conn)})
  | Some {connect=oconn;creq=oreq} ->
	let ncl = (({connect=oconn;creq=(List.append oreq [(r, sw, tw, ty)])})::(remove_elem_list b.conn ({connect=oconn;creq=oreq}))) in
	(Success ("LOG: request sent to " ^ (uri_to_hstring_val (firstElement (Request?.rf r).requrl)) ^ "\n"), {b with conn=ncl})

val getConnection : browser -> connection' -> Tot (option (connReq'))
let getConnection b c = 
  match (List.tryFind (fun ({connect=x;creq=rl}) -> x=c) b.conn) with
  | None -> None
  | Some x -> Some x

(* get the new connection pool after removing the first request for the connection*)
val getResponseConn : connectionPool -> connection -> Tot (option ((request * cowindow * cowindow * navType) * bool * connectionPool))
let getResponseConn cl c =
  match (List.tryFind (fun ({connect=x;creq=rl}) -> x = c) cl) with
  | None -> None
  | Some c -> 
      (match c.creq with
	| [] -> None
	| (req)::tr -> Some (req, c.connect.ccred, (({connect=c.connect;creq=tr})::(remove_elem_list cl c))))
  
val mk_connection : connection' -> Tot connection
let mk_connection c = c

val mk_conn : connection -> Tot connection'
let mk_conn c = c

val getConn : connReq -> Tot connReq'
let getConn c = c

val getConnReq : connReq' -> Tot (option request)
let getConnReq c =
  match c.creq with
  | [] -> None
  | (h,_,_,_)::_ -> Some h





(* *** HEADER PARSING *** *)
(* open ExtFunctionsImpl --- Implemented the ML version. Check Extra folder for the OCaml implementation *)

(* Total version of parseSerialAll *)
private val parseSerial : #l:secLevel -> secString l -> Tot (list (secString l))
let parseSerial #l s = parseSerialAll s

(* from serialized value retrieve the directive name/value*)
val getDirectiveFromString : string -> Tot (option csp_directive)
let getDirectiveFromString s = getDirectiveFromStringAll s

(* from serialized value retrieve the cookie name/value and attributes*)
(* getCookieFromStringAll returns cookieHeader' *)
val getCookieFromString : l:secLevel -> string -> Tot (option (cookieHeader l))
let getCookieFromString l s =
    match getCookieFromStringAll l s with
    | None -> None
    | Some c -> Some c

val emptyHeaderVal : headervalue -> Tot bool
let emptyHeaderVal h = (Headervalue?.hv h = emptyString (Headervalue?.hvs h))

val mk_headerval : #s:secLevel -> secString s -> Tot (headervalue)
let mk_headerval #s t = Headervalue s t

(* Check if the request url is in the secLevel of the URI (or) should we add the origin to the secLevel *)
(* {match (URI?.usl u) with | PublicVal -> true | SecretVal sec -> List.mem (getOrigin (firstElement (Request?.rf r).requrl)) sec} *)
val getHeaderValueURI : r:request -> u:uri -> Tot (h:headervalue) 
let getHeaderValueURI r u = 
  let s = Request?.rsl r in
  let str = declassify (uri_to_hstring #(URI?.usl u) u) in
  Headervalue s (reclassifyVal #PublicVal str s) (* need to reclassify the header value for the URI that will receive it *)

val getHeaderValueOrigin : r:request -> Tot (h:headervalue)
let getHeaderValueOrigin r =
  let s = Request?.rsl r in
  if (TOrigin? (mk_origin (Request?.rf r).reqo)) then Headervalue s (classify #PublicVal (origin_to_string (Request?.rf r).reqo) s)
  else Headervalue s (emptyString s)

private val parseCookieHeaderVal : #s:secLevel -> h:headervalue{Headervalue?.hvs h = s} -> Tot (list (secString s))
let parseCookieHeaderVal #s h = parseSerialCookie (Headervalue?.hv h)

private val parseHeaderVal : #s:secLevel -> h:headervalue{Headervalue?.hvs h = s} -> Tot (list (secString s))
let parseHeaderVal #s h = parseSerial (Headervalue?.hv h)

private val parseLocHeaderVal : #s:secLevel -> h:headervalue{Headervalue?.hvs h = s} -> Tot (secString s)
let parseLocHeaderVal #s h = (Headervalue?.hv h)

(* Check the ABNF to determine how many header field values are allowed for each header *)
(* For multiple values, we assume that the list of origin is empty {List.find (fun (f,v) -> f = hf) h <> None} *) 
(* Also, assume that there are no duplicate field-names (they are probably combined before parsing) *)
private val parseHeader : h:header -> headerfield -> Tot (option headervalue)
let rec parseHeader h hf = 
  match h with
  | [] -> None
  | (f,v)::tl -> if (f=hf) then (Some v)
	       else (parseHeader tl hf)
	       
(* get cookie header from list string*)
private val getCookieFromHeaderList : #s:secLevel -> list (secString s) -> Tot (list (cookieHeader s))
let rec getCookieFromHeaderList #s ls =
  match ls with
  | [] -> []
  | h::t -> (match getCookieFromString s (declassify h) with
	  | None -> (getCookieFromHeaderList t)
	  | Some c -> c::(getCookieFromHeaderList t))

(* get csp_policy from list string*)
private val getCSPDirectivesList : #s:secLevel -> list (secString s) -> Tot csp_policy
let rec getCSPDirectivesList #s ls =
  match ls with
  | [] -> []
  | h::t -> match getDirectiveFromString (declassify h) with (* in ExtFunctions.fsti *)
	  | None -> (getCSPDirectivesList t)
	  | Some d -> d::(getCSPDirectivesList t)

(* Get all the headers' names that are not in the list of header names *)
private val getAllHeadersNotIn : #s:secLevel -> header -> list (secString s) -> Tot (list string)
let rec getAllHeadersNotIn #s h ls =
  match h with
  | [] -> []
  | (n,_)::tl -> if (List.tryFind (fun x -> eqString x n) ls = None) then n::(getAllHeadersNotIn tl ls)
	       else getAllHeadersNotIn tl ls

val reclassifyForbiddenLemma : h:header{checkHeaderSecLevel h} -> u:uri -> Lemma (requires (notForbiddenHeaderfieldInReqHeader h)) 
			       (ensures (notForbiddenHeaderfieldInReqHeader (reclassifySchemeHeader h u))) [SMTPat (reclassifySchemeHeader h u)]
let rec reclassifyForbiddenLemma h u = 
  match h with 
  | [] -> ()
  | (f,v)::tl -> reclassifyForbiddenLemma tl u

(* make the scheme of the request https *)
val makeRequestHTTPS : r:request{notForbiddenHeaderfieldInReqHeader (Request?.rf r).reqhead} -> 
		       Tot (nr:request{notForbiddenHeaderfieldInReqHeader (Request?.rf nr).reqhead}) 
let makeRequestHTTPS r =
  let req = Request?.rf r in
  let u = setURIScheme (firstElement req.requrl) "https" in
  let h = reclassifySchemeHeader req.reqhead u in 
  Request (URI?.usl u) ({req with requrl=[u];reqhead=h;reqbody=reclassifyVal req.reqbody (URI?.usl u)})

(* convert method to string *)
private val toStringMethod : reqMethod -> Tot string
let toStringMethod m = m





(* *** RESPONSE - Definition *** *)
type respuri =
| Failure
| URL of uri

(* private val uriSecLevel : respuri -> GTot bool *)
(* let uriSecLevel r =  *)
(*   match r with *)
(*   | Failure -> true *)
(*   | URL u -> validSingleSecLevel (URI?.usl u)  *)

// RFC 7231 for details of HTTP semantics
// Resp_code 3XX indicates that it is a redirection
// Redirect to another uri - 301, 302, 303, 307
// Redirect request method changes from POST to GET for 301, 302 but NOT for 307
// if resp_code is 200, the status is ok and header contains response data
// if resp_code is 302 (page found) but the origin of the request is not allowed access return error
// if resp_code is 404, page is not found and return error
// Current URL is the first url in respurl if it is not empty
type actResponse' (s:secLevel) = {
  resptype:responseType;
  respcode:nat;
  respurl:list uri;
  resphead:header;
  respbody:secString s;
  resptrail:header;
  respHTTPS:httpstate;
  respCSP:csp_policy;
  respCORS:list headerfield;
  resploc:(option (r:respuri(* {uriSecLevel r} *)));
  respRedSec:secLevel;
}

val isRedirectResponse : #s:secLevel -> actResponse' s -> Tot bool
let isRedirectResponse #s resp =
  (* if (resp.respcode = 301 || resp.respcode = 302 || resp.respcode = 303 || resp.respcode = 307 || resp.respcode = 308) then true *)
  if (resp.respcode >= 300 && resp.respcode <= 399) then true
  else false

private val isValidHeader : s:secLevel -> header -> GTot bool
let isValidHeader s h =
  match s with 
  | PublicVal -> (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) h)  
  | SecretVal sec -> isHeaderVisible h sec 

val isValidResponse : #s:secLevel -> actResponse' s -> GTot bool
let isValidResponse #s r = isValidHeader s r.resphead 
	      
type actResponse =
| ActResponse : arl:secLevel -> ar:actResponse' arl{isValidResponse ar} -> actResponse

(* Use this function to check if the secLevel of the redirect uri is what was expected by the response server *)
private val checkRespSecLevel : resp:(actResponse){(ActResponse?.ar resp).resploc <> None /\ (ActResponse?.ar resp).resploc <> Some Failure} -> GTot bool
let checkRespSecLevel resp =
  match (ActResponse?.ar resp).resploc with
  | Some (URL u) -> equalSubLevels (URI?.usl u) (ActResponse?.ar resp).respRedSec

private val checkLocationURISecLevel : resp:actResponse -> GTot (bool)
let checkLocationURISecLevel resp =
  let (hl) = parseHeader (ActResponse?.ar resp).resphead "Location" in
  match hl with
  | None -> true
  | Some hv -> Headervalue?.hvs hv = (ActResponse?.ar resp).respRedSec

(* Refer to 4.4. URL parsing of url.spec.whatwg.org *)
(* TODO - Do parsing of serialized value with base value as first element in u *)
private val getLocURL : #s:secLevel -> secString s -> list uri -> Tot (option (r:respuri(* {uriSecLevel r} *)))
let getLocURL #s l u = match secstring_to_uri l with | None -> Some Failure | Some v -> Some (URL v)

(* Check if the location header's secLevel is included in the response's secLevel *)
val getLocationURI : resp:actResponse -> Tot (option (r:respuri(* {uriSecLevel r} *)))
let getLocationURI resp =
  let (hl) = parseHeader (ActResponse?.ar resp).resphead "Location" in
  match hl with
  | None -> None 
  | Some hv -> match parseHeaderVal #(Headervalue?.hvs hv) hv with
	      | [] -> None (* TODO - when location header is not present, should we set it to none? *)
	      | h::_ -> (getLocURL h ((ActResponse?.ar resp).respurl))

val isRedResponse : #s:secLevel -> resp:(actResponse' s){isRedirectResponse resp} -> Tot bool
let isRedResponse #s resp =
  if (resp.respcode = 307 || resp.respcode = 308) then true
  else false

(* returns whether the redirect response (307/308) is valid or not -- 
   assume that all redirect responses with code 307/308 should have public requests *)
private val isValidRedirectResp : req:request -> resp:actResponse -> GTot bool
let isValidRedirectResp req resp = 
  if isRedirectResponse (ActResponse?.ar resp) then 
    (checkLocationURISecLevel resp) &&
    (canReclHeader (redirectHeaders (Request?.rf req).reqhead) (ActResponse?.ar resp).respRedSec) &&
    (if isRedResponse (ActResponse?.ar resp) then canReclassify (Request?.rf req).reqbody (ActResponse?.ar resp).respRedSec else true)
  else (ActResponse?.ar resp).resploc = None (* if it is not a redirect response, the resploc field should not be populated *)

private val isValidLocResp : req:request -> resp:actResponse -> GTot bool
let isValidLocResp req resp = 
  match (ActResponse?.ar resp).resploc with 
  | None -> true
  | Some Failure -> true
  | Some (URL u) -> (* (uriSecLevel (URL u)) && *) (checkRespSecLevel resp) && (getLocationURI resp = Some (URL u))
		   
(* A response to request is valid ---
   Check if the redirect response is valid and can be reclassified appropriately and
   Check if the resploc of response is valid (populated by browser using the location header)
*)
val requestResponseValid : request -> actResponse -> GTot bool
let requestResponseValid req resp = (isValidRedirectResp req resp) && (isValidLocResp req resp)

private val isValidRedReclURI : req:request -> resp:actResponse -> GTot bool
let isValidRedReclURI req resp = (canReclHeader (redirectHeaders (Request?.rf req).reqhead) (ActResponse?.ar resp).respRedSec)

(* If a response to request is valid then headers can be reclassified *)
val validRedLemma : req:request -> resp:actResponse -> 
		    Lemma (requires (requestResponseValid req resp /\ isRedirectResponse (ActResponse?.ar resp)))
			  (ensures (isValidRedReclURI req resp))
		    [SMTPat (requestResponseValid req resp)]
let validRedLemma req resp = ()

val reqRespLocLemma : req:request -> resp:actResponse -> 
		      Lemma (requires (requestResponseValid req resp /\ isRedirectResponse (ActResponse?.ar resp))) 
			    (ensures (match (ActResponse?.ar resp).resploc with | None -> true | Some Failure -> true 
				     | Some (URL u) -> (canReclHeader (redirectHeaders (Request?.rf req).reqhead) (URI?.usl u))))
		      [SMTPat (requestResponseValid req resp)]
let reqRespLocLemma req resp = ()

val validRedReqLemma : #s:secLevel -> req:(requestFormat s){not (emptyList req.requrl)} -> 
		       Lemma (requires (let u = (firstElement req.requrl) in (URI?.usl u) = s /\
				       (* (uriSecLevel (URL u)) /\  *)(match (URI?.usl u) with | SecretVal ol -> (isHeaderVisible req.reqhead ol) | _ -> true)))
		       (ensures (isValidRequest req))
let validRedReqLemma #s req = ()

(* safelisted response header names *)
val isSafelistHeader : hf:headerfield -> Tot (b:bool{b = true ==> hf <> "Location"})
let isSafelistHeader hf = (hf="Cache-Control" || hf="Content-Language" || hf="Content-Type" || hf="Expires" || hf="Last-Modified" || hf="Pragma")

val getFilteredHeader : header -> Tot header
let rec getFilteredHeader h =
  match h with
  | [] -> []
  | (n,v)::tl -> if (isForbiddenRespHeader n) then getFilteredHeader tl
	       else (n,v)::(getFilteredHeader tl)

val filteredHeaderLemma : h:header -> Lemma (requires True) (ensures (forall x. List.mem x (getFilteredHeader h) ==> List.mem x h)) 
			  [SMTPat (getFilteredHeader h)]
let rec filteredHeaderLemma h = 
  match h with
  | [] -> ()
  | hd::tl -> filteredHeaderLemma tl
  
val filteredRespLemma : s:list torigin -> h:header -> Lemma (requires  (isHeaderVisible h s)) 
			(ensures ((isHeaderVisible (getFilteredHeader h) s))) (* [SMTPat (getFilteredHeader h)] *)
let rec filteredRespLemma s h = 
  match h with
  | [] -> ()
  | hd::tl -> filteredRespLemma s tl

val filteredPublicLemma : h:header -> Lemma (requires (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) h)) 
			  (ensures (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) (getFilteredHeader h))) [SMTPat (getFilteredHeader h)]
let rec filteredPublicLemma h = match h with | [] -> () | hd::tl -> filteredPublicLemma tl

(* CORS-safelisted response-header name, given a header, CORS-exposed header-name list(ch) *)
val getSafelistedHeader : h:header -> list headerfield -> Tot (fh:header{forall x. List.mem x fh ==> List.mem x h})
let rec getSafelistedHeader h ch =
  match h with
  | [] -> []
  | (n,v)::tl -> if (isSafelistHeader n) || (List.mem n ch && not (isForbiddenRespHeader n)) then (n,v)::(getSafelistedHeader tl ch)
	       else (getSafelistedHeader tl ch)

val safeRespLemma : s:list torigin -> h:header -> l:list headerfield -> 
		    Lemma (requires (isHeaderVisible h s)) (ensures (isHeaderVisible (getSafelistedHeader h l) s)) 
let rec safeRespLemma s h l = 
  match h with
  | [] -> ()
  | hd::tl -> safeRespLemma s tl l

val headerListValue : header -> headerfield -> Tot (option headervalue)
let rec headerListValue h hf =
  match h with 
  | [] -> None
  | (f,v)::tl -> if f = hf then Some v else headerListValue tl hf

val validSLemma : h:header -> l:list headerfield -> Lemma (requires (emptyList (getSafelistedHeader h l))) 
		  (ensures (headerListValue (getSafelistedHeader h l) "Location" = None)) [SMTPat (getSafelistedHeader h l)]
let rec validSLemma h l = 
  match (getSafelistedHeader h l) with
  | [] -> ()
  | hd::tl -> validSLemma tl l

val subLocLemma : h:header -> l:list headerfield -> Lemma (requires (not (List.mem "Location" l))) 
			  (ensures (headerListValue (getSafelistedHeader h l) "Location" = None)) [SMTPat (getSafelistedHeader h l)]
let rec subLocLemma h l = 
  match h with
  | [] -> ()
  | (f,v)::tl -> subLocLemma tl l 

val safePublicLemma : h:header -> l:list headerfield -> Lemma (requires (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) h)) 
			  (ensures (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) (getSafelistedHeader h l))) [SMTPat (getSafelistedHeader h l)]
let rec safePublicLemma h l = match h with | [] -> () | hd::tl -> safePublicLemma tl l

(* basic filtered response*)
val basicResponse : actResponse -> Tot (actResponse)
let basicResponse resp =
  let nh = (match (ActResponse?.arl resp) with
	     | PublicVal -> getFilteredHeader (ActResponse?.ar resp).resphead
	     | SecretVal sec -> 
		 (
		 filteredRespLemma sec (ActResponse?.ar resp).resphead);
		 getFilteredHeader (ActResponse?.ar resp).resphead ) in
  ActResponse (ActResponse?.arl resp) ({(ActResponse?.ar resp) with resptype="basic";resphead=nh;})

(* cors filtered response*)
val corsResponse : actResponse -> Tot (actResponse)
let corsResponse resp =
  match (ActResponse?.arl resp) with
  | PublicVal -> 
      let nh = getSafelistedHeader (ActResponse?.ar resp).resphead (ActResponse?.ar resp).respCORS in
      ActResponse (ActResponse?.arl resp) ({(ActResponse?.ar resp) with resptype="cors";resphead=nh})
  | SecretVal sec ->
      (safeRespLemma sec (ActResponse?.ar resp).resphead (ActResponse?.ar resp).respCORS);
      let nh = getSafelistedHeader (ActResponse?.ar resp).resphead (ActResponse?.ar resp).respCORS in
      ActResponse (ActResponse?.arl resp) ({(ActResponse?.ar resp) with resptype="cors";resphead=nh})
  (* ActResponse "cors" resp.respcode resp.respurl nh resp.respbody resp.resptrail resp.respHTTPS resp.respCSP resp.respCORS resp.resploc *)

(* opaque filtered response*)
val opResponse : resp:actResponse -> Tot (actResponse)
let opResponse resp =
  ActResponse PublicVal ({(ActResponse?.ar resp) with resptype="opaque";respcode=0;respurl=[];resphead=[];respbody="";resptrail=[]})

(* opaque redirect filtered response*)
val opRedResponse : resp:actResponse -> Tot (actResponse)
let opRedResponse resp =
  ActResponse PublicVal ({(ActResponse?.ar resp) with resptype="opaqueredirect";respcode=0;resphead=[];respbody="";resptrail=[]})

type filteredresponse = {
  ir:actResponse;
  fr:actResponse;
}

(* type basicfilteredresponse = b:filteredresponse{b.fr = (basicResponse b.ir)} *)

(* type corsfilteredresponse = c:filteredresponse{c.fr = (corsResponse c.ir)} *)

(* type opaqfilteredresponse = o:filteredresponse{o.fr = (opResponse o.ir)} *)

(* type opaqRedfilteredresponse = or:filteredresponse{or.fr = (opRedResponse or.ir)} *)

type filteredResponse =
| BasicFiltered : f:filteredresponse{f.fr = (basicResponse f.ir)} -> filteredResponse
| CORSFiltered : f:filteredresponse{f.fr = (corsResponse f.ir)} -> filteredResponse
| OpaqFiltered : f:filteredresponse{f.fr = (opResponse f.ir)} -> filteredResponse
| OpaqRedFiltered : f:filteredresponse{f.fr = (opRedResponse f.ir)} -> filteredResponse

type response =
| RespSuccess of pubString
| NetworkError of pubString
| TotResponse : t:actResponse -> response
| FilteredResponse : fr:filteredResponse -> response

val validReqResp : request -> response -> GTot bool
let validReqResp req res =
  match res with 
  | TotResponse resp -> requestResponseValid req resp
  | FilteredResponse fr -> let iresp = (match fr with
			  | BasicFiltered b -> b.ir
			  | CORSFiltered c -> c.ir
			  | OpaqFiltered o -> o.ir
			  | OpaqRedFiltered orf -> orf.ir ) in
			  requestResponseValid req iresp
  | _ -> true
  
type resource =
| RequestResource : req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> resource (*For urls, use default_request using the current window and url*)
| ResponseResource : req:request -> resp:response{validReqResp req resp} -> resource





(* *** Response-header parsing *** *)
val getCSPDirectives : resp:actResponse -> Tot csp_policy
let getCSPDirectives resp =
  let l = (parseHeader (ActResponse?.ar resp).resphead "Content-Security-Policy") in
  (match l with | None -> [] | Some v -> getCSPDirectivesList #(Headervalue?.hvs v) (parseHeaderVal v))
  
(* Section 5.9 - CORS check *)
(* missing check for "null" -- not defined in the spec *)
val corsCheck : req:request -> resp:actResponse -> Tot bool
let corsCheck req resp =
  let nreq = (Request?.rf req) in
  let l = parseHeader (ActResponse?.ar resp).resphead "Access-Control-Allow-Origin" in
  match l with 
  | None -> false (* origin is null *)
  | Some v -> 
      let hvorigin = parseHeaderVal #(Headervalue?.hvs v) v in
      if (nreq.reqcredm <> "include" && hvorigin = [(classify #PublicVal "*" (Headervalue?.hvs v))]) then true
      else if (singleValue hvorigin && (classify #PublicVal (origin_to_string nreq.reqo) (Headervalue?.hvs v) <> firstElement hvorigin)) then false
      else if (nreq.reqcredm <> "include") then true
      else (
	let lc = parseHeader (ActResponse?.ar resp).resphead "Access-Control-Allow-Credentials" in 
	match lc with 
	| None -> false
	| Some cv -> (
	    let cred = parseHeaderVal #(Headervalue?.hvs cv) cv in
	    if (singleValue cred && firstElement cred = classify #PublicVal "true" (Headervalue?.hvs cv)) then true else false))

private val corsOKResponse1 : req:request -> resp:actResponse -> Tot (option actResponse)
let corsOKResponse1 req resp = 
  let nreq = (Request?.rf req) in
  if (List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) then None
  else if (List.for_all (fun (n,_) -> isCORSSafeReqHeader n) nreq.reqhead) = false then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

private val corsOKResponse2 : req:request -> resp:actResponse -> vh:headervalue -> Tot (option actResponse)
let corsOKResponse2 req resp vh = 
  let nreq = (Request?.rf req) in
  let (hheaders) = parseHeaderVal #(Headervalue?.hvs vh) vh in 
  if (List.tryFind (fun x -> eqString x "*") hheaders <> None) && (nreq.reqcredm = "include") then None
  else if ((List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) && 
      (List.tryFind (fun x -> eqString x "Authorization") hheaders = None)) then None
  else if (List.for_all (fun n -> isCORSSafeReqHeader n) (getAllHeadersNotIn nreq.reqhead hheaders) = false &&
      List.tryFind (fun x -> eqString x "*") hheaders = None) then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

private val corsOKResponse3 : #l:secLevel -> request -> actResponse -> list (secString l) -> Tot (option actResponse)
let corsOKResponse3 #l req resp hmethods = 
  let nreq = (Request?.rf req) in
  if ((List.tryFind (fun x -> eqString x "*") hmethods <> None) && nreq.reqcredm = "include") then None
  else if ((List.tryFind (fun x -> eqString x (toStringMethod nreq.reqm)) hmethods = None) && 
      (List.tryFind (fun x -> eqString x "*") hmethods = None) && (nreq.reqm <> "GET") && (nreq.reqm <> "POST") && (nreq.reqm <> "HEAD")) then None
  else if (List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) then None
  else if (List.for_all (fun (n,_) -> isCORSSafeReqHeader n) nreq.reqhead) = false then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

private val corsOKResponse4 : #l:secLevel -> request -> actResponse -> headervalue -> list (secString l) -> Tot (option actResponse)
let corsOKResponse4 #l req resp vh hmethods = 
  let nreq = (Request?.rf req) in
  let (hheaders) = parseHeaderVal #(Headervalue?.hvs vh) vh in 
  if ((List.tryFind (fun x -> eqString x "*") hmethods <> None || List.tryFind (fun x -> eqString x "*") hheaders <> None) && nreq.reqcredm = "include") then None
  else if ((List.tryFind (fun x -> eqString x (toStringMethod nreq.reqm)) hmethods = None) && (List.tryFind (fun x -> eqString x "*") hmethods = None) &&
	  (nreq.reqm <> "GET") && (nreq.reqm <> "POST") && (nreq.reqm <> "HEAD")) then None
  else if ((List.tryFind (fun (n,v) -> n = "Authorization") nreq.reqhead <> None) && (List.tryFind (fun x -> eqString x "Authorization") hheaders = None)) then None
  else if (List.for_all (fun n -> isCORSSafeReqHeader n) (getAllHeadersNotIn nreq.reqhead hheaders) = false && List.tryFind (fun x -> eqString x "*") hheaders = None) then None
  else Some resp (* return the response ; check for the appropriate max-age and set in the CORS-preflight cache*)

(* Step 7 of Section 5.7 *)
val corsOKResponse : req:request -> resp:actResponse -> Tot (option actResponse)
let corsOKResponse req resp =
  let nreq = (Request?.rf req) in
  let lm = parseHeader (ActResponse?.ar resp).resphead "Access-Control-Allow-Methods" in
  let lh = parseHeader (ActResponse?.ar resp).resphead "Access-Control-Allow-Headers" in
  match lm with
  | None ->  
      let hmeth = if (nreq.reqpreflight) then [(toStringMethod nreq.reqm)] else [] in
      if ((List.tryFind (fun x -> x = (toStringMethod nreq.reqm)) hmeth = None) && (List.tryFind (fun x -> x = "*") hmeth = None) &&
	 (nreq.reqm <> "GET") && (nreq.reqm <> "POST") && ((Request?.rf req).reqm <> "HEAD")) then None
      else 
      (
	match lh with
	| None -> corsOKResponse1 req resp     
	| Some vh -> corsOKResponse2 req resp vh
      )
  | Some vm -> let (hmethods) = parseHeaderVal #(Headervalue?.hvs vm) vm in 
	      match lh with
	      | None -> corsOKResponse3 req resp hmethods
	      | Some vh -> corsOKResponse4 req resp vh hmethods

(* fs returns the last valid policy token *)
private val getRefPolicyToken: #s:secLevel -> list (secString s) -> string -> Tot string
let rec getRefPolicyToken #s hp fs =
  match hp with
  | [] -> fs
  | hd::t ->
	 if (eqString hd "no-referrer") then getRefPolicyToken t "no-referrer"
	 else if (eqString hd "no-referrer-when-downgrade") then getRefPolicyToken t "no-referrer-when-downgrade"
	 else if (eqString hd "strict-origin") then getRefPolicyToken t "strict-origin"
	 else if (eqString hd "strict-origin-when-cross-origin") then getRefPolicyToken t "strict-origin-when-cross-origin"
	 else if (eqString hd "same-origin") then getRefPolicyToken t "same-origin"
	 else if (eqString hd "origin") then getRefPolicyToken t "origin"
	 else if (eqString hd "origin-when-cross-origin") then getRefPolicyToken t "origin-when-cross-origin"
	 else if (eqString hd "unsafe-url") then getRefPolicyToken t "unsafe-url"
	 else getRefPolicyToken t fs

(* Referrer Policy --- 8.1. Parse a referrer policy from a Referrer-Policy header *)
val parseRefPol : actResponse -> Tot refPolicy
let parseRefPol resp =
  let (hrpl) = parseHeader (ActResponse?.ar resp).resphead "Referrer-Policy" in (* ABNF : 1#policy-token - assuming # to mean at least 1? *)
  match hrpl with
  | None -> RP_EmptyPolicy
  | Some hv -> 
      let hrp = parseHeaderVal #(Headervalue?.hvs hv) hv in
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

val getExposeHeaders : actResponse -> Tot (list (headerfield))
let getExposeHeaders r = 
    let s = parseHeader (ActResponse?.ar r).resphead "Access-Control-Expose-Headers" in 
    match s with
    | None -> []
    | Some v -> declassify_list (parseHeaderVal #(Headervalue?.hvs v) v) 
	       	   




(* *** COOKIES *** *)
(* Unable to equate cookies as they can have different levels based on chost flag *)
private val get_old_cookie : #s:(secLevel){s <> PublicVal} -> (c_cookie s) -> cs:(list cookie) -> Tot (option cookie)
let rec get_old_cookie #s c cs =
  match cs with
  | [] -> None
  | ch::ct -> let a = (Cookie?.c ch) in 
	    if (declassify a.cname = declassify c.cname && a.cdom = c.cdom && declassify_list a.cpath = declassify_list c.cpath) then Some ch
	    else get_old_cookie c ct

val httpOnly : cookie -> Tot bool
let httpOnly c = (Cookie?.c c).chttp

val createTime : cookie -> Tot string
let createTime c = (Cookie?.c c).ccreate

(* Set cookie for the origin and replace only if same cookie is present for that origin *)
private val set_cookie_in_store : browser -> c:cookie -> (option cookie) -> Tot browser
let set_cookie_in_store b c rc =
  match rc with
  | Some oc -> {b with cookieStore=(c::(remove_elem_list b.cookieStore oc))} (* replace old with new. TODO - set new's creation to old *)
  | None -> {b with cookieStore=(c::b.cookieStore)}

(* Return only visible cookie list based on origin *)
private val get_cookies_from_store : u:uri -> (list cookie) -> Tot (l:(list cookie){List.for_all (fun c -> isCookieOriginMatch (getOrigin u) (Cookie?.c c)) l})
let rec get_cookies_from_store u lc =
  match lc with
  | [] -> []
  | c::tlc -> if (isCookieOriginMatch (getOrigin u) (Cookie?.c c)) then c::(get_cookies_from_store u tlc)
	    else (get_cookies_from_store u tlc)

(* Get current time for setting certain cookie attributes *)
(* Probably, not required unless clearing cookies *)
val curtime : string
let curtime = "1234" (* string_of_int (get_cur_time) *)

(* Take the domain cookie attribute and a request uri and return the appropriate cookie domain along with the host-only flag *)
(* 4.1.2.3 - RFC 6265 *)
private val get_cdomain_val : list cookieAttribute -> o:torigin -> Tot (option (bool * h:hdomain{domainMatch (TOrigin?.host o) h}))
let get_cdomain_val ca o =
  let da = List.tryFind (fun a -> match a with | Cdomain _ -> true | _ -> false) ca in
  match da with 
  | Some (Cdomain cd) -> 
      if (domainMatch (TOrigin?.host o) cd && not (emptyList cd)) then 
	 (match cd with | _::tl -> if not (emptyList tl) then Some (false, cd) else None)
      else None
  | None -> (match (TOrigin?.host o) with | [] -> None | _::tl -> if not (emptyList tl) then Some (true, (TOrigin?.host o)) else None)
  | _ -> None

(* retrieve the expires/max-age attribute from the cookie header*)
private val get_cexpires_val : list cookieAttribute -> Tot (bool * string)
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
private val get_cpath_val : #s:secLevel{s <> PublicVal} -> list cookieAttribute -> uri -> Tot (path s)
let get_cpath_val #s ca u =
  let pa = List.tryFind (fun a -> match a with | Cpath _ -> true | _ -> false) ca in
  match pa with
  | Some (Cpath cp) -> mk_list_string #s cp
  | None -> recPath #(URI?.usl u) (getPath u) s
  | _ -> []

(* Get the cookie's secure-only value from the secureonly attribute *)
private val get_csecure_val : list cookieAttribute -> Tot bool
let get_csecure_val ca =
  let sa = List.tryFind (fun a -> match a with | SecureOnly -> true | _ -> false) ca in
  match sa with
  | Some (SecureOnly) -> true
  | None -> false
  | _ -> false

(* Get the cookie's http-only value from the httponly attribute *)
private val get_chttp_val : list cookieAttribute -> Tot bool
let get_chttp_val ca =
  let ha = List.tryFind (fun a -> match a with | HttpOnly -> true | _ -> false) ca in
  match ha with
  | Some (HttpOnly) -> true
  | None -> false
  | _ -> false

private val getSubDomains : h:hdomain{match h with | [] -> false | _::tl -> not (emptyList tl)} -> torigin -> Tot (t:(list torigin){not (emptyList t)})
let rec getSubDomains h o =
  match h with
  | hd::tl -> if singleValue tl then [(TOrigin (TOrigin?.protocol o) h (TOrigin?.port o) (TOrigin?.dom o))]
	    else (TOrigin (TOrigin?.protocol o) h (TOrigin?.port o) (TOrigin?.dom o))::(getSubDomains tl o) (* Do not include top-level domain *)

private val getCookieOrigins : bool -> hd:hdomain{match hd with | [] -> false | _::tl -> not (emptyList tl)} -> o:torigin{domainMatch (TOrigin?.host o) hd} -> 
			       Tot (t:(list torigin){not (emptyList t)})
let getCookieOrigins ho hd o = 
  let h = (TOrigin (TOrigin?.protocol o) hd (TOrigin?.port o) (TOrigin?.dom o)) in
  if ho then [h] else (getSubDomains hd o)

private val setCookieAux : #s:secLevel{s <> PublicVal} -> b:browser -> u:uri -> c:c_cookie s -> nhapi:bool -> Tot browser
let setCookieAux #s b u c nhapi = 
	if (c.chttp = true && (nhapi = true || ((getScheme u) <> "http" && (getScheme u) <> "https")))
	  then b (* cookie had http-only set but not received from http(s) scheme or non-HTTP API; ignore *)
        else
          let cp = get_old_cookie c b.cookieStore in
	  match cp with 
	  | None -> set_cookie_in_store b (Cookie s c) (None) 
	  | Some oc -> 
	      if (c.chttp = false && (httpOnly oc)) then b (* old cookie was http-only and new is not; ignore *)
	      else let nc = {c with ccreate=(createTime oc)} in
		   set_cookie_in_store b (Cookie s nc) (Some oc) 

(* Section 5.3 of RFC6265 *)
(* Use the last set values - reverse the list when checking. List.tryFind returns the first found element? *)    
(* sets the cookie details in the browser's cookie store *)
(* u is the uri from which the cookie was received *)
(* nhapi indicates if the set-cookie is called from a non-HTTP API -> true indicates a non-HTTP API *)
private val set_cookie : #l:secLevel -> b:browser -> u:uri -> ch:(cookieHeader l) -> nhapi:bool -> Tot browser
let set_cookie #l b u ch nhapi = 
    let cattr = ch.cookie_attr in
    let alist = List.rev cattr in 
    match (get_cdomain_val alist (getOrigin u)) with 
    | None -> b
    | Some (ho, hd) -> 
      let ol = getCookieOrigins ho hd (getOrigin u) in
      let s = SecretVal ol in 
      let n = classify #PublicVal (declassify ch.cookie_name) s in
      let v = classify #PublicVal (declassify ch.cookie_value) s in
      let (pf, exp) = get_cexpires_val alist in 
      let c = {cname=n;cval=v;cexp=exp;cdom=hd;cpath=(get_cpath_val #s alist u);ccreate=curtime;cla=curtime;cpersist=pf;chost=ho;csec=(get_csecure_val alist);chttp=(get_chttp_val alist)} in
      setCookieAux #s b u c nhapi 
		   
(* (\* Section 5.4 of RFC6265 *\) *)
(* u is the uri to which the request is being sent *)
(* CookieStore should be sorted with longer paths before shorter paths when sending. If equal-length then earlier creation time*)
(* Update the last-access time of the cookie in the store to current time -- Useful when removing cookies *)
private val get_cookies : u:uri -> cs:(list cookie){List.for_all (fun c -> isCookieOriginMatch (getOrigin u) (Cookie?.c c)) cs} -> nhapi:bool -> 
			  Tot (l:(list cookie_send)(* {forall x. List.mem x l ==> (URI?.usl u = (CookieSend?.csl x))} *))
let rec get_cookies u cs nhapi =
  let rh = (TOrigin?.host (getOrigin u)) in
  let prot = (TOrigin?.protocol (getOrigin u)) in
  match cs with
  | [] -> []
  | c::tl ->
    let hc = (Cookie?.c c) in
    if ((recPath hc.cpath (URI?.usl u)) = (getPath u) || (pathMatch (getPath u) (recPath hc.cpath (URI?.usl u)))) then (* request path path-matches cookie-path*)
       let s = (URI?.usl u) in
       let cs = (declassify hc.cname, declassify hc.cval) in (* Need some lemma here?? *)
       (if (hc.csec = true && prot = "https") then (*using only https for now, should add other secure schemes*)
	 (if hc.chttp = true && nhapi = false && (prot = "https" || prot = "http") then (*httponly flag set and http(s) scheme*)
	     cs::(get_cookies u tl nhapi)
	  else if hc.chttp = false then cs::(get_cookies u tl nhapi) (*httponly flag not set*)
	  else (get_cookies u tl nhapi)) (*httponly flag set but not http(s) scheme or non-http API *)
	else if hc.csec = false then (*secureonly flag not set*)
	  (if hc.chttp = true && (prot = "https" || prot = "http") then (*httponly flag set and http(s) scheme*)
	      cs::(get_cookies u tl nhapi)
	   else if hc.chttp = false then cs::(get_cookies u tl nhapi) (*httponly flag not set*)
	   else (get_cookies u tl nhapi)) (*httponly flag set but not http(s) scheme*)
	else (get_cookies u tl nhapi)) (*secureonly flag set and non-secure scheme*)
    else (get_cookies u tl nhapi) (* path does not match *)

private val serialize_string : s:secLevel -> (list cookie_send)(* {forall x. List.mem x l ==> ((CookieSend?.csl x) = s)} *) -> Tot (secString s)
let rec serialize_string s cl =
  match cl with
  | [] -> emptyString s
  | (cn,cv)::tc -> let c = cn ^ "=" ^ cv ^ ";" in strcat (classify #PublicVal c s) (serialize_string s tc)

(* Serialize the cookie list into string *)
private val serialize_cookie_list : s:secLevel -> l:(list cookie_send) -> Tot (headervalue)
let serialize_cookie_list s l = Headervalue s (serialize_string s l)

(* Get the cookie-list as a string*)
val get_cookie_list : b:browser -> r:request -> bool -> Tot headervalue
let get_cookie_list b r nhapi =
  let u = firstElement (Request?.rf r).requrl in
  let cl = get_cookies u (get_cookies_from_store u b.cookieStore) nhapi in
  serialize_cookie_list (Request?.rsl r) cl

(* Set all the cookies in the cookieHeader list from response based on set_cookie algorithm *)
private val setCookieBrowser : #s:secLevel -> list (cookieHeader s) -> browser -> u:uri -> Tot browser
let rec setCookieBrowser #s lc b u =
  match lc with
  | [] -> b
  | hd::tl -> let nb = (set_cookie b u hd false) in
	    setCookieBrowser tl nb u

(* set the cookies in the browser from the response *)
val setCookie : browser -> req:request -> resp:actResponse{requestResponseValid req resp} -> Tot browser
let setCookie b req resp =
  let u = (firstElement (Request?.rf req).requrl) in
  let l = (parseHeader (ActResponse?.ar resp).resphead "Set-Cookie") in  (* s is the list of string and o is the list of origin*)
  match l with
  | None -> b
  | Some v -> let c = getCookieFromHeaderList (parseCookieHeaderVal #(Headervalue?.hvs v) v) in
	     setCookieBrowser #(Headervalue?.hvs v) c b u





(* *** CSP *** *)
private val origin_match_expr_source : torigin -> dirValue -> torigin -> nat -> Tot bool
let origin_match_expr_source ro dv orig redir =
  match dv with
  | DV_Any -> if TOrigin?.protocol ro = "http" || TOrigin?.protocol ro = "https" || TOrigin?.protocol ro = TOrigin?.protocol orig then true else false
  | DV_Self -> if (orig = ro) || (TOrigin?.host orig = TOrigin?.host ro && (TOrigin?.protocol orig = "http" && TOrigin?.protocol ro = "https")) (* check for ports *) then true
	      else false
  | DV_Scheme p -> if p = TOrigin?.protocol ro || (p = "http" && TOrigin?.protocol ro = "https") then true else false
  | DV_Origin o -> if o.op_prot <> TOrigin?.protocol ro && (not (o.op_prot = "http" && TOrigin?.protocol ro = "https")) then false
		  else if o.op_prot = "" && (TOrigin?.protocol orig <> TOrigin?.protocol ro) &&
		    (not (TOrigin?.protocol orig = "http" && TOrigin?.protocol ro = "https")) then false
		  else if (not (domainMatch o.op_host (TOrigin?.host ro))) then false
		  (* else if  --- check for ports here *)
		  else if (o.op_path <> [] && redir = 0) then false (* path is [] for origin *)
		  else true
  | _ -> false

val origin_match_expr_source_list : uri -> list dirValue -> uri -> nat -> Tot bool
let rec origin_match_expr_source_list r ls origU redir =
  let ro = getOrigin r in
  let orig = getOrigin origU in
  if (OOrigin? ro) then false
  else
  match ls with
  | [] -> false
  | hd::tl -> if (origin_match_expr_source ro hd orig redir) then true (* if matches return matches else check other values *)
	    else origin_match_expr_source_list r tl origU redir

(* 6.6.1.5. Does url match source list in origin with redirect count? *)
(* It is not clear what happens with multiple dirValues starting from 'none' or 'none' in between?
   Currently, it seems the desired behavior is to allow checks on other dirValues
*)
(* Check for every expression in the dirValue list
   redir is the redirection count
*)
private val uri_match_expr_source : uri -> dirValue -> torigin -> nat -> Tot bool
let uri_match_expr_source u dv orig redir =
  let ro = getOrigin u in
  match dv with
  | DV_Any -> if TOrigin?.protocol ro = "http" || TOrigin?.protocol ro = "https" || TOrigin?.protocol ro = TOrigin?.protocol orig then true else false
  | DV_Self -> if (orig = ro) || (TOrigin?.host orig = TOrigin?.host ro && (TOrigin?.protocol orig = "http" && TOrigin?.protocol ro = "https")) (* check for ports *) then true
	      else false
  | DV_Scheme p -> if p = TOrigin?.protocol ro || (p = "http" && TOrigin?.protocol ro = "https") then true else false
  | DV_Origin o -> if o.op_prot <> TOrigin?.protocol ro && (not (o.op_prot = "http" && TOrigin?.protocol ro = "https")) then false
		  else if o.op_prot = "" && (TOrigin?.protocol orig <> TOrigin?.protocol ro) &&
		    (not (TOrigin?.protocol orig = "http" && TOrigin?.protocol ro = "https")) then false
		  else if (not (domainMatch o.op_host (TOrigin?.host ro))) then false
		  (* else if  --- check for ports here *)
		  else if (o.op_path <> [] && redir = 0) then
		      (if (o.op_em = true && getPath u <> (mk_list_string #(URI?.usl u) o.op_path)) then false
		      else if (not (pathMatch (getPath u) (mk_list_string #(URI?.usl u) o.op_path))) then false
		      else true)
		  else true
  | _ -> false

private val uri_match_expr_source_list : r:uri -> list dirValue -> orig:torigin -> nat -> Tot bool
let rec uri_match_expr_source_list r ls orig redir =
  match ls with
  | [] -> false
  | hd::tl -> if (uri_match_expr_source r hd orig redir) then true (* if matches return matches else check other values *)
	    else uri_match_expr_source_list r tl orig redir

(* 6.6.1.3. Does request match source list? *)
(* match the request url with the directive value given the request's origin and redirect count - CSP*)
val uri_match_source : lu:(list uri){not (emptyList lu)} -> list dirValue -> orig:a_origin -> nat -> Tot bool
let uri_match_source lu ls orig redir =
  if (OOrigin? orig) then false
  else
  match lu with
  | u::_ ->
    match ls with
    | [] -> false
    | [DV_None] -> false
    | _ -> uri_match_expr_source_list u ls orig redir

(* 6.6.1.4. Does response to request match source list? *)
(* match the response url with the directive value given the request's origin and redirect count - CSP*)
val uri_match_resp_source : lu:list uri -> list dirValue -> orig:a_origin -> nat -> Tot bool
let uri_match_resp_source lu ls orig redir =
  if (OOrigin? orig) then false
  else
  match lu with
  | [] -> false (* although this should not be possible, for sanity check *)
  | u::_ -> match ls with
	  | [] -> false
	  | [DV_None] -> false
	  | _ -> uri_match_expr_source_list u ls orig redir
	  




(* DECLASSIFIERS *)
private val getURI : #s:secLevel -> browser -> cowindow -> u:uri{URI?.usl u = s} -> Tot (option (c_uri s))
let getURI #s b cw u = (get_c_uri b cw u)

private val getWindow : browser -> cowindow -> cowindow -> Tot (option window)
let getWindow b cw tw = if isSameOriginWin cw tw then Some (cowin_to_win tw) else None

private val getHeaderVal : #s:secLevel -> hv:headervalue{(Headervalue?.hvs hv) = s} -> Tot (secString s)
let getHeaderVal #s hv = (Headervalue?.hv hv)

(* Server functions *)
private val parseReqHeader : h:header -> hf:headerfield -> Tot (option headervalue)
let rec parseReqHeader h hf = 
  match h with
  | [] -> None
  | (f,v)::tl -> if (f=hf) then (Some v)
	       else (parseReqHeader tl hf)

val s_getHeaderValueString : #s:secLevel -> h:headervalue{Headervalue?.hvs h = s} -> Tot (secString s)
let s_getHeaderValueString #s h = getHeaderVal h

val s_getURI : #s:secLevel -> u:uri{URI?.usl u = s} -> Tot (c_uri s)
let s_getURI #s u = (u_curi u)

val s_getReqHeaderValue : request -> headerfield -> Tot (list string)
let s_getReqHeaderValue req h =
  match (parseReqHeader (Request?.rf req).reqhead h) with
  | None -> []
  | Some v -> let s = (if (h = "Cookie") then parseCookieHeaderVal #(Headervalue?.hvs v) v else parseHeaderVal #(Headervalue?.hvs v) v) in
	     declassify_list s
  
val s_getRequestURI : #s:secLevel -> req:request{(URI?.usl (firstElement (Request?.rf req).requrl)) = s} -> Tot (c_uri s)
let s_getRequestURI #s req = u_curi (firstElement (Request?.rf req).requrl)

val s_getRequestOrigin : request -> Tot origin
let s_getRequestOrigin req = (mk_origin (Request?.rf req).reqo)

val s_getURISecLevel : #s:secLevel -> c_uri s -> Tot (l:secLevel{l = s})
let s_getURISecLevel #s u = s

val s_getReqURISecLevel : request  -> Tot (l:secLevel)
let s_getReqURISecLevel req = (URI?.usl (firstElement (Request?.rf req).requrl))

val s_getRequestBody : #s:secLevel -> req:request{Request?.rsl req = s} -> Tot (secString s)
let s_getRequestBody #s req = (Request?.rf req).reqbody

val s_secstring_uri: #l:secLevel -> secString l -> Tot (option (torigin * a_uri l))
let s_secstring_uri #l s = (hstring_to_curi_ml l (declassify s)) 
