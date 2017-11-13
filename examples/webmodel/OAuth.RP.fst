(*
  Defines the functionality of the RP in the OAuth protocol
*)
module OAuth.RP

open FStar.All
open FStar.Ref
open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.StringFunctions
open Browser.Model.Interface
open Network.Interface
open OAuth.Datatypes

#reset-options "--z3rlimit 100"

(* ***** RP.COM ***** *)
let rpurl = ({c_origin=rpori;c_uname=emptyString (SecretVal [rpori]);c_pwd=emptyString (SecretVal [rpori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [rpori])})
let rpuri = mk_uri rpurl

(* data related to different ips - already present through registration *)
val rpCD : (FStar.ST.ref clientData)
let rpCD = ST.alloc [(ipori, clientIDRPIP, clientSecretRPIP)]

val rpLS : (FStar.ST.ref loginSession)
let rpLS = ST.alloc [] 

val getRPClientID : torigin -> St (option (s:secretVal{Secret?.s s = PublicVal}))
let getRPClientID t = getClientID (!rpCD) t  

(* (\* use a browser for sending request containing authcode from RP to IP at the end of the protocol *\) *)
(* val rpbr : (ref browser) *)
(* let rpbr = ST.alloc (init_browser)  *)
(* let irp = match (set_unique_id !rpb) with | (f, s) -> rpb := s; f (\* Get a unique_id (f) and browser (s) *\) *)
(* let rpdoc = {dloc=rpuri;dref=blank_uri;dori=(mk_aorigin rpurl.c_origin);dHTTPS="none";drefPol=RP_OriginWhenCO;dCSP=[];dsbox=[];} *)
(* (\* create a window in the browser to send the request with "rpdoc" as the document *\) *)
(* let rpsw =  *)
(*       let hist = HistEntry (URI?.usl rpuri) (URI?.u rpuri) get_time rpdoc irp in  *)
(*       let newwin = (win_to_cowin ({winid=irp;wname="";wloc=rpuri;wframes=[];wopener=None;wparent=None;whist={hlhe=[hist];hcur=1};wdoc=(rpdoc);wsbox=[];})) in *)
(*       (rpb := ({(!rpb) with windows=newwin::(!rpb).windows})); newwin *)

(* send the initial login request to the IP *)
val rpLoginIPAuth : r:browserRequest -> ML (resp:actResponse{requestResponseValid r resp}) 
let rpLoginIPAuth r =
  let urisl = (BRequest?.rsl r) in
  let ruri = (firstElement (BRequest?.rf r).requrl) in (* get the request url *)
  let qs = getQS ruri in
  let ip = getQSVal #urisl qs "IP" in
  if s_equal #urisl #PublicVal ip "ip" then 
  (
    let sl = (SecretVal [rpori;ipori]) in 
    let sid = (genSecret sl) in
    let state = (genSecret sl) in 
    match (getRPClientID ipori) with
    | None -> (print_string ("Error: Client id not found\n" ); (defErrResponse rpori (BRequest?.rf r).reqb))
    | Some clid ->
    (
      let cid = declassify #PublicVal (getSecret clid) in 
      (let logsession:loginSession = [(ipori, sid, state)] in
      rpLS := List.append logsession (!rpLS));
      let respuri = ({c_origin=ipori;c_uname=emptyString sl;c_pwd=emptyString sl;c_path=[classify #PublicVal "authEP" sl];c_querystring=[(classify #PublicVal "client_id" sl,classify #PublicVal cid sl);(classify #PublicVal "redirect_uri" sl, classify #PublicVal "https://rp.com:443/codeEP/" sl);(classify #PublicVal "origin" sl, classify #PublicVal "https://rp.com:443/" sl);(classify #PublicVal "csrftoken" sl,getSecret state)];c_fragment=emptyString sl}) in
      let rpREP = curi_to_hstring respuri in 
      let rpResp = ActResponse sl ({respori=rpori;respdest=(BRequest?.rf r).reqb;resptype="default";respcode=301;respurl=[]; resphead=[("Set-Cookie", (mk_svheaderval sid));("Location", (mk_headerval rpREP))]; respbody=(emptyString sl);resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=sl}) in
      (rpResp)
      ))
  else if s_equal #urisl #PublicVal ip "badip" then 
  (
    let sl = (SecretVal [rpori;badipori]) in
    let sid = (genSecret sl) in
    let state = (genSecret sl) in
    match (getRPClientID ipori) with (* getting ipori's client_id as the badip will replace it eventually *)
    | None -> (print_string ("Error: Client id not found\n" ); (defErrResponse rpori (BRequest?.rf r).reqb))
    | Some clid ->
    (
      let cid = declassify #PublicVal (getSecret clid) in 
      (let logsession:loginSession = [(badipori, sid, state)] in
      rpLS := List.append logsession (!rpLS));
      (* Badip replaces the response headers as per its convenience - the badip can modify the origin-index also  *)
      let usl = (SecretVal [rpori;ipori]) in
      let respuri = ({c_origin=ipori;c_uname="";c_pwd="";c_path=["authEP"];c_querystring=[("client_id",cid);("redirect_uri","https://rp.com:443/codeEP/");("origin","https://rp.com/");("csrftoken",declassify #sl (getSecret state))];c_fragment=""}) in
      let rpREP = classify #PublicVal (curi_to_hstring respuri) usl in
      let rpResp = ActResponse usl ({respori=rpori;respdest=(BRequest?.rf r).reqb;resptype="default";respcode=301;respurl=[]; resphead=[("Set-Cookie", (mk_headerval (classify #PublicVal (declassify #sl (getSecret sid)) usl)));("Location", (mk_headerval rpREP))]; respbody=(emptyString usl);resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=usl}) in
      print_string ("IP is not ip.com:" ^ (curi_to_hstring respuri) ^ "\n" );
      (rpResp)
      ))
  else (print_string ("IP is not ip.com:" ^ (declassify ip) ^ "\n" ); (defErrResponse rpori (BRequest?.rf r).reqb))


val getRPLoginIPAuth : r:browserRequest -> ML (ret:retReqResp{isValidRetResp (BrowserRequest r) ret})
let getRPLoginIPAuth r = (let resp = rpLoginIPAuth r in RetResponse resp)


(* Compact authcode resend method for the RP *)
val rpReqCodeEP : browserRequest ->  ML (option (sr:serverRequest{notForbiddenHeaderfieldInReqHeader (SRequest?.srf sr).sreqhead}))
let rpReqCodeEP r =
  let urisl = (BRequest?.rsl r) in
  let ruri = (firstElement (BRequest?.rf r).requrl) in (* get the request url *)
  let qs = getQS #urisl (ruri) in
  let csrftoken = mk_secretval (getQSVal #urisl qs "csrftoken") in
  let actualIP = mk_secretval (getQSVal #urisl qs "Issuer") in
  let ip = getIPLogin !rpLS csrftoken in (* determine the IP based on the state-token *)
  if (ip = blank_origin) then
    (None)
  else if ((declassify #urisl (getSecret actualIP)) = (origin_to_string ip)) then
    (
    let urisl = SecretVal [ip] in
    let code = declassify (getQSVal #(URI?.usl ruri) qs "authcode") in
    match (getRPClientID ip) with
    | None -> (print_string ("Error: Client id not found with req-code\n" ); None)
    | Some clid ->
	let cid = declassify #PublicVal (getSecret clid) in
	(match (getCDSecret (!rpCD) ip) with
	| None -> (* get client data secret is none for the ip -- may be the client_secret was not established *)
	   (
	   (* The port is required to pass isOriginSec in StringFunctions *)
	   let rturi = ({c_origin=ip;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),(classify #PublicVal code urisl))];c_fragment=emptyString urisl}) in
	   let nreq = SRequest urisl ({sreqm = "POST"; srequrl = [(mk_uri rturi)]; sreqhead = []; sreqo = rpori; sreqtype = ""; sreqnonce = ""; sreqmode = NoCORS; sreqbody = (emptyString urisl);}) in
	   Some nreq
	   )
	| Some sec ->
	   (
	   secretOriginLemma ip (Secret?.s sec);
	   let cs = classify #(Secret?.s sec) (getSecret #(Secret?.s sec) (sec)) urisl in
	   let rturi = ({c_origin=ip;c_uname=emptyString urisl;c_pwd=emptyString urisl;c_path=[(classify #PublicVal "tokenEP" urisl)];c_querystring=[((classify #PublicVal "client_id" urisl), classify #PublicVal cid urisl);((classify #PublicVal "redirect_uri" urisl),(classify #PublicVal "https://rp.com:443/codeEP/" urisl));((classify #PublicVal "authcode" urisl),(classify #PublicVal code urisl));((classify #PublicVal "client_secret" urisl),cs)];c_fragment=emptyString urisl}) in
	   let nreq = SRequest urisl ({sreqm = "POST"; srequrl = [(mk_uri rturi)]; sreqhead = []; sreqo = rpori; sreqtype = ""; sreqnonce = ""; sreqmode = NoCORS; sreqbody = (emptyString urisl);}) in
	   Some nreq
	   )))
  else (print_string ("Error: The IP does not match\n"); None)


val getRPReqCodeEP : r:browserRequest -> ML (ret:retReqResp{isValidRetResp (BrowserRequest r) ret})
let getRPReqCodeEP r = (match rpReqCodeEP r with | None -> RetResponse (defErrResponse rpori (BRequest?.rf r).reqb) | Some req -> RetRequest (ServerRequest req))


(* For different requests, return different responses *)
val rpReqResp : req:anyRequest -> ML (ret:retReqResp{isValidRetResp req ret})
let rpReqResp req =
    match req with 
    | BrowserRequest r ->
	let urisl = (BRequest?.rsl r) in
	let ruri = (firstElement (BRequest?.rf r).requrl) in (* get the request url *)
	if (getPort ruri) = (Some 443) then (* Only accept secure connections (HTTPS) *)
	(
	if (checkEP r "login-ipauth") then (* if the end-point is login with IP *)
	  (getRPLoginIPAuth r)
	else if (checkEP r "codeEP") then (* auth-code end-point *)
	  (getRPReqCodeEP r)
	else (RetResponse (defErrResponse rpori (BRequest?.rf r).reqb))
	)
	else (print_string ("Insecure connection: \n" ); (* " ^ (declassify (curi_to_hstring (s_getRequestURI #urisl r))) ^ " *)
	  (RetResponse (defErrResponse rpori (BRequest?.rf r).reqb)))
    | ServerRequest r -> 
	  (RetResponse (defErrResponse rpori (SRequest?.srf r).sreqo)) (* Impossible case*)

  
