// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.

module Microsoft.FStar.Tests.Test

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax

let test_iset () =
    let iset1 = new_set<int>(fun x y -> x=y) (fun x -> x) 
    let iset2 = new_set<int>(fun x y -> x=y) (fun x -> x) 
    for i in 1..10 do
        ignore <| set_add i iset1
    done     
    for i in 1..20 do
        ignore <| set_add i iset2
    done
    printfn "Set 1 is %A" (set_elements iset1)
    printfn "Set 2 is %A" (set_elements iset2)
    printfn "Subset? 1, 2= %A" (set_is_subset_of iset1 iset2)
    printfn "Subset? 2, 1= %A" (set_is_subset_of iset2 iset1)
    
let test_freevars () =
    Options.print_real_names := true
    let iset1 = Syntax.new_ftv_set () 
    let iset2 = Syntax.new_ftv_set ()
    printfn "Empty set subset? %A" (set_is_subset_of iset1 iset2)
    for i in 1..10 do
        let x = Util.new_bvd None 
        let y = {ppname=Syntax.mk_ident("junk", int64 i); 
                 realname=Syntax.mk_ident(x.realname.idText, 1L)}
        ignore <| set_add (Util.bvd_to_bvar_s x Syntax.tun) iset1
        ignore <| set_add (Util.bvd_to_bvar_s y Syntax.tun) iset2
    done 
    printfn "Set 1 is %A" (set_elements iset1 |> List.map (fun x -> Print.strBvd x.v))
    printfn "Set 2 is %A" (set_elements iset2 |> List.map (fun x -> Print.strBvd x.v))
    printfn "Subset? 1, 2= %A" (set_is_subset_of iset1 iset2)
    printfn "Subset? 2, 1= %A" (set_is_subset_of iset2 iset1)

[<EntryPoint>]
let main argv = 
    //test_iset()
    test_freevars ()
//    printfn "%A" argv
    0 // return an integer exit code
