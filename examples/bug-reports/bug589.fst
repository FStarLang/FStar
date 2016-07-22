module Bug589

//Extraction suceeds when using any of these annotations:
//val f: list 'a -> unit
//let f (#a:Type) (l:list a) =
//let f (l:list 'a) =
let f l =
  let rec aux l =
    match l with
    | [] -> ()
    | hd::tl -> aux tl
  in
  aux l

(*
$ bin/fstar.exe --codegen OCaml examples/bug-reports/bug589.fst
Extracting module FStar.PredicateExtensionality
Extracting module FStar.TSet
Extracting module FStar.Heap
Extracting module FStar.ST
Extracting module FStar.All
Extracting module Bug589
Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Failure("(./examples/bug-reports/bug589.fst(1,13-13,7)) bound Variable uu___#480 not found\n")
*)
