module OAuth.User

open FStar.All
open FStar.Heap
open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.StringFunctions
open Browser.Model.Interface
open NetworkRequestInterface
open OAuth.Datatypes
open OAuth.RP
open OAuth.IP

val anyReqResp : r:request -> Tot (ret:retReqResp{isValidRetResp r ret})
let anyReqResp r = RetResponse defResponse

val getResponse : o:torigin{List.mem o trustedOrigins} -> ML (r:request -> ML (ret:retReqResp{isValidRetResp r ret}))
let getResponse o =
  if (o = rpori) then rpReqResp
  else if (o = ipori) then ipReqResp
  else anyReqResp

val getProcResponse : o:origin -> ML (r:request -> ML (ret:retReqResp{isValidRetResp r ret}))
let getProcResponse o = 
  if (TOrigin? o && List.mem o trustedOrigins) then getResponse o
  else anyReqResp

let b = (init_browser)
let (i, nb) = (set_unique_id b)

(* Window's origin - RP to log into *)
let ori = TOrigin "https" ["rp";"com"] (Some 443) None
let durl = {c_origin=ori;c_uname=emptyString (SecretVal [ori]);c_pwd=emptyString (SecretVal [ori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [ori])}
let duri = mk_uri durl
let doc = {dloc=duri;dref=blank_uri;dori=(mk_aorigin durl.c_origin);dHTTPS="none";drefPol=RP_NoReferrer;dCSP=[];dsbox=[];}
let (sw, cb) = 
      let hist = HistEntry (URI?.usl duri) (URI?.u duri) get_time doc i in 
      let newwin = (win_to_cowin ({winid=i;wname="";wloc=duri;wframes=[];wopener=None;wparent=None;whist={hlhe=[hist];hcur=1};wdoc=(doc);wsbox=[];})) in
      (newwin, ({(nb) with windows=newwin::(nb).windows}))

let sl = (SecretVal [rpori])
(* Request's URL - RP's server *)
let rurl = {c_origin=rpori;c_uname=emptyString sl;c_pwd=emptyString sl;c_path=[(classify #PublicVal "login-ipauth" sl)];c_querystring=[(classify #PublicVal "IP" sl),(classify #PublicVal "ip.com" sl)];c_fragment=emptyString sl}
let ruri = mk_uri rurl
(* Request to start OAuth authentication *)
let newreq = Request sl ({reqm = "POST"; requrl = [ruri]; reqhead = []; reqo = (mk_aorigin (URI?.u (CWindow?.cwloc sw)).c_origin); reqw = (Some sw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client sw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = emptyString sl; corsflag = false; corspfflag = false; authflag = false; recflag = false})

(* Username and password for IP *)
let uname = classify #PublicVal "usernameU" (SecretVal [ipori])
let pass = classify #PublicVal "passwordP" (SecretVal [ipori])

val print_result : result -> ML unit
let print_result r =
  match r with 
  | Error e -> print_string ("Error: " ^ e ^ "\n")
  | Success s -> print_string ("Success: " ^ s ^ "\n")

val processRPResponse : req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> ML (result * browser) 
let processRPResponse req = 
  let pr' = (getProcResponse rpori) req in
  match pr' with
  | RetRequest nreq -> (let co = {cori=ipori;ccred=true} in
		      match (getConnection !rpb co) with (* the rp creates a new request here - sent to the ip *)
		      | None -> (Error ("No connections available!"), !rpb)
	   	      | Some ({connect=oconn;creq=oreq}) -> 
			     let pr'' = (getProcResponse ipori) nreq in
			     (match pr'' with 
			     | RetRequest _ -> (Error ("No response from ipori!"), !rpb) 
			     | RetResponse pr -> let (res, _, _, nb) = processResponse !rpb oconn nreq pr in 
						(res,nb)))
  | RetResponse _ -> (Error ("No request made from RP to IP!"), !rpb) 

(* Process the response from the IP after authentication *)
val processIPResponse : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> ML (result * browser) 
let processIPResponse ib req =
    let co = {cori=ipori;ccred=true} in
    match (getConnection ib co) with
    | None -> (Error ("No connections available!"), ib)
    | Some ({connect=oconn;creq=oreq}) ->
	let pr' = (getProcResponse ipori) req in
	match pr' with
	| RetRequest _ -> (Error ("No connections available!"), ib)
	| RetResponse pr ->
	    let (res, nr, _, nb) = processResponse ib oconn req pr in 
	    (
	    print_result res; 
	    match nr with
	    | None -> (Success ("No more requests!"), nb)
	    | Some nreq -> processRPResponse nreq)
			  (* (let pr = (getProcResponse rpori) nreq in *)
			  (* match (getConnection !rpb co) with (\* the rp creates a new request here - sent to the ip *\) *)
			  (* | None -> (Error ("No connections available!"), !rpb) *)
			  (* | Some ({connect=oconn;creq=oreq}) -> ( *)
			  (* 	 match (oreq) with  *)
			  (* 	 | [] -> (Error ("No requests on connection for IP!"), !rpb) *)
			  (* 	 | (rq,_,_,_)::_ -> ((\* remove the headers that should not be a part of request (redirect) *\) *)
			  (* 	     let nrq = (Request (Request?.rsl rq) ({(Request?.rf rq) with reqhead=(redirectHeaders (Request?.rf rq).reqhead)})) in *)
			  (* 	     let pr = (getProcResponse ipori) nrq in *)
			  (* 	     let (res, _, _, nb) = processResponse !rpb oconn nrq pr in  *)
			  (* 	     (res, !rpb))))) *)

let ipsl = SecretVal [ipori]
let formurl = {c_origin=ipori;c_uname=emptyString ipsl;c_pwd=emptyString ipsl;c_path=[(classify #PublicVal "authEP" ipsl)];c_querystring=[];c_fragment=emptyString ipsl}
let formuri = mk_uri formurl

val processIPFormResponse : browser -> req:request{notForbiddenHeaderfieldInReqHeader (Request?.rf req).reqhead} -> connection -> ML (result * browser)
let processIPFormResponse br r oconn =
  let pr'' = (getProcResponse ipori) r in
  match pr'' with 
  | RetRequest _ -> (Error ("Request should not occur."), br)
  | RetResponse pr -> let (res, nr', w, nbr) = processResponse br oconn r pr in (* response from ip processed - requires submission of form*)
	(print_result res;
	match w with
	| None ->  (Error ("No executable window!\n"), nbr)
	| Some sw -> 
	    (let qsfd = [(classify #PublicVal "user" ipsl, classify #PublicVal "usernameU" ipsl);(classify #PublicVal "pwd" ipsl, classify #PublicVal "passwordP" ipsl)] in
	    let (_, nr', _, nb) = form_submission nbr (cowin_to_win sw) "" "POST" formuri qsfd in
	    match nr' with 
	    | None -> (Error ("No proper request!\n"), nbr)
	    | Some req -> processIPResponse nb req))

let browserOAuth () : ML (result * browser) =
  let (r, _, nw, nb) = open_window cb sw "https://rp.com/" "" in
  let (re, nr, win, sb) = navigateWindow (nb) sw nw (RequestResource newreq) "other" in
  match sb.conn with (*the response arrives on the connection - assume connection is the first available here*)
  | [] -> (Error ("No connections"), sb)
  | hd::_ ->
      let pr' = (getProcResponse rpori) newreq in
      match pr' with
      | RetRequest _ -> (Error ("No proper response!"), sb)
      | RetResponse pr -> let (r1, nr, _, br) = processResponse sb (getConn hd).connect newreq pr in (* Processes response from RP that redirects to IP *)
	  (print_result r1;
	  let co = {cori=ipori; ccred=true} in
	  match (getConnection br co) with
	  | None -> (Error ("No connections after response from RP to IP"), br)
	  | Some ({connect=oconn;creq=oreq}) -> (
		 match nr with 
		 | None -> (Error ("No requests made here"), br)
		 | Some nreq -> processIPFormResponse br nreq oconn))

(* Request's URL - RP's server - Assuming that the initial request was for "ip.com" but attacker modified it to "badip.com" *)
(* Everything else happens at ip.com *)
let birurl = {c_origin=rpori;c_uname=emptyString sl;c_pwd=emptyString sl;c_path=[(classify #PublicVal "login-ipauth" sl)];c_querystring=[(classify #PublicVal "IP" sl),(classify #PublicVal "badip.com" sl)];c_fragment=emptyString sl}
let biruri = mk_uri birurl
(* Request to start OAuth authentication *)
let bireq = Request sl ({reqm = "POST"; requrl = [biruri]; reqhead = []; reqo = (mk_aorigin (URI?.u (CWindow?.cwloc sw)).c_origin); reqw = (Some sw); reqinit = ""; reqtype = ""; reqdest = ""; reqtarget = None; reqredirect = 0; reqredmode = "follow"; reqref = (Client sw); reqrefPolicy = RP_OriginWhenCO; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = emptyString sl; corsflag = false; corspfflag = false; authflag = false; recflag = false})

(* let ipMixUp () : ML (result * browser) =  *)
(*   let (r, nw, nb) = open_window cb sw "https://rp.com/" "" in *)
(*   let (re, win, sb) = navigateWindow (nb) sw nw (RequestResource bireq) "other" in  *)
(*   match sb.conn with (\*the response arrives on the connection - assume connection is the first available here*\) *)
(*   | [] -> (Error ("No connections"), sb) *)
(*   | hd::_ -> *)
(*       let pr = (getProcResponse rpori) bireq in *)
(*       let (r1, _, br) = processResponse sb (getConn hd).connect pr in (\* Processes response from RP that redirects to IP *\) *)
(*       ( *)
(*       print_result r1; *)
(*       let co = {cori=ipori; ccred=true} in *)
(*       match (getConnection br co) with *)
(*       | None -> (Error ("No connections after response from RP to IP"), br) *)
(*       | Some ({connect=oconn;creq=oreq}) -> ( *)
(* 	  match (oreq) with  *)
(* 	  | [] -> (Error ("No requests on the connection after response from RP to IP"), br) *)
(* 	  | (rq,_,_,_)::_ -> *)
(* 	      let pr = (getProcResponse ipori) rq in *)
(* 	      let (res, w, nbr) = processResponse br oconn pr in (\* response from ip processed - requires submission of form*\)  *)
(* 	      ( *)
(* 	      print_result res; *)
(* 	      match w with  *)
(* 	      | None ->  (Error ("No executable window!\n"), nbr)  *)
(* 	      | Some sw -> let (_, _, nb) = form_submission nbr (cowin_to_win sw) "" "POST" None [("user","usernameU");("pwd","passwordP")] in *)
(* 			  processIPResponse nb *)
(* 			  ))) *)
			  
let main =
    let (r,nb) = browserOAuth () in
    print_result r
	    
