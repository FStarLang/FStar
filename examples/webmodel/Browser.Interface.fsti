module Browser.Interface

open Web.Origin
open Web.URI
open Secret.SecString
open Browser.Datatypes
open Browser.Model.Interface
open Browser.AuxiliaryDatatypes

type execWindow = sw:window{List.find (fun w -> w = SB_Script) sw.wsbox = None}

val getAllWindows : b:browser -> Tot (list cowindow)

val getWin : cowindow -> Tot (option execWindow)

val getDocumentDomain : browser -> execWindow -> Tot (hdomain)

val setDocumentDomain : browser -> execWindow -> hdomain -> Tot (browser * cowindow)

val getWinLocation : #s:secLevel -> browser -> execWindow -> cowindow -> Tot (option (c_uri s))

val setWinLocation : browser -> execWindow -> cowindow -> u:uri{match (URI?.usl u) with | SecretVal [o] -> true | _ -> false} -> Tot browser

val getLocalStorageItem : browser -> execWindow -> key:string -> Tot string

val setLocalStorageItem : browser -> execWindow -> key:string -> value:string -> Tot browser

val postMessage : browser -> execWindow -> cowindow -> msg:string -> target:string -> Tot result

val getWinByName : browser -> execWindow -> winname:string -> Tot (browser * cowindow)

val winOpen : browser -> execWindow -> uri:string -> winname:string -> Tot (browser * cowindow)

val winClose : browser -> execWindow -> cowindow -> Tot browser

val formSubmit : browser -> execWindow -> target:string -> reqMethod -> submituri:uri -> formdata:list (string * string) -> Tot browser 

val xhr: browser -> execWindow -> xhruri:uri -> reqMethod -> body:string -> headers:header -> Tot browser
