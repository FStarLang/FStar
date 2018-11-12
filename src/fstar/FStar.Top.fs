#light "off"
module FStar.Top
open FStar.ST
open FStar.All
let _ =
    let t = (new System.Threading.Thread(FStar.Main.main, 1024 * 1024 * 32)) in
    t.Start() ; t.Join() ;
    printfn "done"
