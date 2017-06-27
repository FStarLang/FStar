(*
  Testing the content security policy feature of the browser - both positive and negative tests
  Run "make ocaml_csp"
*)
module Example.ContentSecurityPolicy

open FStar.IO
open Secret.SecString
open Web.Origin
open Web.URI
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.AuxiliaryDatatypes
open Browser.ContentSecurityPolicy
open ML.ExternalFunctions

let dori = TOrigin "https" ["idp";"com"] (Some 443) None
let sl = (SecretVal [dori])

let dcuri = ({c_origin=dori;c_uname=(emptyString sl);c_pwd=(emptyString sl);c_path=[];c_querystring=[];c_fragment=(emptyString sl)})
let durl = URI sl dcuri

let opath = {op_prot="https"; op_host=["rp";"com"]; op_port=Some 443; op_dom=None; op_path=[];op_em=true}

(* self is dori, i.e., the document's origin *)
let list_dir_valueD = [DV_Self;(DV_Origin opath)]
let list_dir_valueC = [DV_None]
let cspDirD = {dir_name=CSP_default_src;dir_value=list_dir_valueD} (*allow request*) (* default results to connect depending on the type of request*)
let cspDirC = {dir_name=CSP_connect_src;dir_value=list_dir_valueC} (*disallow request*)
let cspPol = [cspDirD]

(* create a document and window containing that document with the csp policy above *)
let doc = {dloc=durl;dref=blank_uri;dori=(mk_aorigin blank_origin);dHTTPS="none";drefPol=RP_EmptyPolicy;dCSP=cspPol;dsbox=[]}

let sw = {winid=noWin;wname="";wloc=durl;wframes=[];wopener=None;wparent=None;whist=({hlhe=[( HistEntry sl (mk_auri dcuri) get_time doc noWin)];hcur=1});wdoc=doc;wsbox=[];}
let csw = win_to_cowin sw

let rorigin = TOrigin "https" ["rp";"com"] (Some 443) None
let rsl = (SecretVal [rorigin])
let rcuri = {c_origin=rorigin;c_uname=(emptyString rsl);c_pwd=(emptyString rsl);c_path=[];c_querystring=[];c_fragment=(emptyString rsl)}
let rurl = URI rsl rcuri

let req = Request (rsl) ({reqm = "GET"; requrl = [rurl]; reqhead = []; reqo = (getAOrigin sw.wloc); reqw = (Some csw); reqinit = "fetch"; reqtype = ""; reqdest = "subresource"; reqtarget = (Some csw); reqredirect = 0; reqredmode = "follow"; reqref = (Client csw); reqrefPolicy = RP_EmptyPolicy; reqnonce = ""; reqparser = ""; requnsafe = false; reqpreflight = false; reqsync = false; reqmode = NoCORS; reqtaint = "basic"; reqcredm = "omit"; reqcredflag = false; reqbody = (classify #PublicVal "username:u;password:p" rsl); corsflag = false; corspfflag = false; authflag = false; recflag = false})

let main =
  if reqBlockedCSP req then
    print_string ("Blocked!\n")
  else
    print_string ("Hello F*!\n")
