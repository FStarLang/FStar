#light "off"
module FStar.Top
open FStar.Compiler.Effect
open FStar.Compiler.Effect
let _ =
    let t = (new System.Threading.Thread(FStar.Main.main, 1024 * 1024 * 32)) in
    t.Start() ; t.Join()
