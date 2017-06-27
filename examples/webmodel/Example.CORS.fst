(*
  Test example for CORS feature - both positive and negative
  Run "make ocaml_cors"
*)
module Example.CORS

open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open Browser.Model.Interface

let ori:torigin = TOrigin "https" ["rp";"com"] (Some 443) None

let ib = (init_browser)
let (i,b) = (set_unique_id ib)
let durl = {c_origin=ori;c_uname=emptyString (SecretVal [ori]);c_pwd=emptyString (SecretVal [ori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [ori])}
let duri = mk_uri durl
let doc = {dloc=duri;dref=blank_uri;dori=(mk_aorigin durl.c_origin);dHTTPS="none";drefPol=RP_NoReferrer;dCSP=[];dsbox=[];}      
let sw:window = let hist = HistEntry (URI?.usl duri) (URI?.u duri) get_time doc i in 
	 ({winid=i;wname="";wloc=duri;wframes=[];wopener=None;wparent=None;whist={hlhe=[hist];hcur=1};wdoc=(doc);wsbox=[];})
let nb = ({b with windows=(win_to_cowin sw)::(b.windows)})

let reqori = TOrigin "https" ["ip";"com"] (Some 443) None
let requrl = {c_origin=reqori;c_uname=emptyString (SecretVal [reqori]);c_pwd=emptyString (SecretVal [reqori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [reqori])}
let requri = mk_uri requrl

(* Assume response as getResp *)
let getResp =
    (* FAILS CORS CHECK *)
    let ipResp = ({resptype="default";respcode=200;respurl=[];resphead=[];respbody=(emptyString (SecretVal [reqori]));resptrail=[];respHTTPS="modern";respCSP=[];respCORS=[];resploc=None}) in
    (* INCLUDES CREDENTIALS - SET INCLUDE TO FAIL THIS *)
    (* let ipResp = ({resptype="default";respcode=200;respurl=[];resphead=[("Access-Control-Allow-Origin", (mk_headerval (SecretVal [reqori]) (classify #PublicVal (origin_to_string (ori)) (SecretVal [reqori]))))];respbody=(emptyString (SecretVal [reqori]));resptrail=[];respHTTPS="modern";respCSP=[];respCORS=[];resploc=None}) in *)
    (* let ipResp = ({resptype="default";respcode=200;respurl=[];resphead=[("Access-Control-Allow-Origin", (mk_headerval (SecretVal [reqori]) (classify #PublicVal (origin_to_string (ori)) (SecretVal [reqori])))); ("Access-Control-Allow-Credentials", (mk_headerval (SecretVal [reqori]) (classify #PublicVal ("true") (SecretVal [reqori]))))];respbody=(emptyString (SecretVal [reqori]));resptrail=[];respHTTPS="modern";respCSP=[];respCORS=[];resploc=None}) in *) 
    ActResponse (SecretVal [reqori]) ipResp

let main =
  let (re, req, w, sb) = xmlHttpRequest nb sw requri "GET" "" [] in  (* this changes the CORS flag to true - open facebook in another window *)
  match sb.conn with (*the response arrives on the connection - assume connection available here*) 
  | [] -> print_string ("Empty F*!\n")
  | hd::_ ->
    let (res, _, wi, br) = processResponse sb (getConn hd).connect req getResp in
    ( match res with
    | (Error e) -> print_string ("Error! " ^ e ^ "\n")
    | (Success s) -> print_string ("Success! " ^ s ^ "\n"))

