// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.

module Microsoft.FStar.Tests.Test

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax

type Boxed<'a> (value:'a, cmp:'a -> 'a -> int, hash: 'a -> int) = 
   member this.unbox = value
   override this.Equals (other:obj) = let y = other :?> Boxed<'a> in cmp value (y.unbox) = 0
   override this.GetHashCode() = hash value
   interface System.IComparable with
            member this.CompareTo(other:obj) = 
                let x = other :?> Boxed<'a> in 
                cmp value (x.unbox)


open System.Collections.Generic
type hset<'value>=HashSet<'value>
type EqCmp<'a> (eq:'a -> 'a -> bool, hash:'a -> int) =
    interface System.Collections.Generic.IEqualityComparer<'a> with
            member this.Equals(x:'a, y:'a) = eq x y
            member this.GetHashCode(x:'a) = hash x
let new_hset (eq:'a -> 'a -> bool) (hash:'a -> int) : hset<'a> = 
    let cmp = new EqCmp<'a>(eq,hash) :> IEqualityComparer<'a> in
    new HashSet<'a>(cmp)
let hset_add a (s:hset<'a>) = ignore <| s.Add(a); s
let hset_remove a (s:hset<'a>) = ignore <| s.Remove(a); s
let hset_mem a (s:hset<'a>) = s.Contains(a)
let hset_copy (s:hset<'a>)  = 
    let s' = new HashSet<'a>(s.Comparer) in
    s'.UnionWith(s); 
    s'
let hset_union (s1:hset<'a>) (s2:hset<'a>) : hset<'a> = s1.UnionWith(s2); s1
let hset_intersect (s1:hset<'a>) (s2:hset<'a>) : hset<'a> = s1.IntersectWith(s2); s2
let hset_elements (s1:hset<'a>) : list<'a> = 
    let mutable e = s1.GetEnumerator() in
    let mutable res =  [] in
        while e.MoveNext() do
          res <- e.Current :: res
        done;
        res 
let hset_is_subset_of (s1:hset<'a>) (s2:hset<'a>) : bool = s1.IsSubsetOf(s2)
let hset_difference (s1:hset<'a>) (s2:hset<'a>) : hset<'a> = s1.ExceptWith(s2); s1
let hset_count (s1:hset<'a>) = s1.Count
let mk_ftv_hset<'a,'b> () : hset<bvar<'a,'b>> = 
    new_hset (fun x y -> bvd_eq x.v y.v) (fun x -> Util.hashcode x.v.realname.idText)
 

type fset<'a> = Collections.Set<Boxed<'a>> * ('a -> Boxed<'a>)
let mk_ftv_fset<'a,'b> () : fset<bvar<'a,'b>> = 
    let box v = new Boxed<bvar<'a,'b>>(v, (fun x y -> x.v.realname.idText.CompareTo(y.v.realname.idText)), (fun x -> Util.hashcode x.v.realname.idText)) in
    (new Collections.Set<Boxed<bvar<'a,'b>>>([]), box)

let fset_add a ((s, b):fset<'a>) = s.Add (b a), b
let fset_remove a ((s1, b):fset<'a>) = s1.Remove(b a), b
let fset_mem a ((s, b):fset<'a>) = s.Contains (b a)
let fset_copy (s:fset<'a>) = s
let fset_union ((s1, b):fset<'a>) ((s2, _):fset<'a>) = Set.union s1 s2, b
let fset_intersect ((s1, b):fset<'a>) ((s2, _):fset<'a>) = Set.intersect s1 s2, b
let fset_subset ((s1, _): fset<'a>) ((s2, _):fset<'a>) = s1.IsSubsetOf(s2)
let fset_count ((s1, _):fset<'a>) = s1.Count
let fset_difference ((s1, b):fset<'a>) ((s2, _):fset<'a>) : fset<'a> = Set.difference s1 s2, b
let fset_elements ((s1, b):fset<'a>) :list<'a> = Set.toList s1 |> List.map (fun x -> x.unbox)


type iset<'a,'b> = {
    name:string;
    add: 'a -> 'b -> 'b;
    mem: 'a -> 'b -> bool;
    union: 'b -> 'b -> 'b;
    copy: 'b -> 'b;
}

let hset_to_iset () : iset<'a, hset<'a>> = {
    name="HashSet";
    add=hset_add;
    mem=hset_mem;
    union=hset_union;
    copy=hset_copy
}

let fset_to_iset () : iset<'a, fset<'a>> = {
    name="F# set";
    add=fset_add;
    mem=fset_mem;
    union=fset_union;
    copy=fset_copy
}

let bench_set (s1:'set, s2:'set, f:iset<bvvar, 'set>, vars:option<bvvar>[]) =
    let timer = System.Diagnostics.Stopwatch.StartNew()
    for i in 0..99999 do
        ignore <| f.add (vars.[i] |> Util.must) s1
    for i in 0..99999 do
        if (i % 2 = 0)
        then  ignore <| f.add (vars.[i] |> Util.must) s2

    printfn "%s: add in %fs" f.name timer.Elapsed.TotalSeconds
        
    timer.Restart()
    for i in 0..1000 do
        ignore <| f.union (f.copy s2) s1

    printfn "%s: copy/union in %fs" f.name timer.Elapsed.TotalSeconds

    timer.Restart()
    for _ in 1..10 do
        for i in 0..99999 do
        ignore <| f.mem (Util.must vars.[i]) s1

    printfn "%s: contains in %fs" f.name timer.Elapsed.TotalSeconds

let set_vs_fset () = 
    let s1 = mk_ftv_hset ()
    let s2 = mk_ftv_hset ()
    let vars = Array.create<bvvar option> 100000 None
    for i in 0..99999 do
        vars.[i] <- Some (Util.bvd_to_bvar_s (Util.new_bvd None) Syntax.tun)

    bench_set (s1, s2, hset_to_iset(), vars);
    let s1 = mk_ftv_fset () in
    let s2 = mk_ftv_fset () in 
    bench_set (s1, s2, fset_to_iset(), vars)

let test_freevars () =
    Options.print_real_names := true
    let iset1 = Syntax.new_ftv_set () 
    let iset2 = Syntax.new_ftv_set ()
    printfn "Empty set subset? %A" (Util.set_is_subset_of iset1 iset2)
    for i in 1..10 do
        let x = Util.new_bvd None 
        let y = {ppname=Syntax.mk_ident("junk", int64 i); 
                 realname=Syntax.mk_ident(x.realname.idText, 1L)}
        ignore <| Util.set_add (Util.bvd_to_bvar_s x Syntax.tun) iset1
        ignore <| Util.set_add (Util.bvd_to_bvar_s y Syntax.tun) iset2
    done 
    printfn "Set 1 is %A" (Util.set_elements iset1 |> List.map (fun x -> Print.strBvd x.v))
    printfn "Set 2 is %A" (Util.set_elements iset2 |> List.map (fun x -> Print.strBvd x.v))
    printfn "Subset? 1, 2= %A" (Util.set_is_subset_of iset1 iset2)
    printfn "Subset? 2, 1= %A" (Util.set_is_subset_of iset2 iset1)

[<EntryPoint>]
let main argv = 
    set_vs_fset()
    0 // return an integer exit code
