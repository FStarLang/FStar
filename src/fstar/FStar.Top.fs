#light "off"
module FStar.Top
open FStar.All
let _ =
#if CUSTOM_STACK_SIZE
    let t = (new System.Threading.Thread(FStar.Main.main, 1048576 * 32)) in
    t.Start() ; t.Join() ;
#else
    let _ = FStar.Main.main () in
#endif
    printfn "done"

