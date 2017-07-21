module GenWrapper

(* Generate Wrappers *)
open Manifest
open FStar.IO
open FStar.HyperStack.ST


val discard: bool -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string s)
unfold val trace: s:string -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let debug = true
unfold let trace = if debug then print else (fun _ -> ())


let type_is_ref = function
    | ABuffer _ -> true
    | _ -> false

val is_deep_ref: (stat:bool)->(arg:argtype) -> ST bool
(requires (fun _ -> True))
(ensures (fun h0 r h1 -> h0 == h1))
let rec is_deep_ref (stat:bool) = function
    |ABuffer a -> if stat then true else is_deep_ref true a
    | _ -> false
    
val print_type: argtype -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let rec print_type = function
 |ANat64 -> trace " int "
 |AChar  -> trace " char "
 |AVoid  -> trace " unit "
 |ABuffer a -> let _ = trace "(reference " in
              let _ = print_type a in
              trace ")"

(* function to allocate stack references if required *)
val allocate_stack_ref: int -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let rec allocate_stack_ref nrefs =                    
      if nrefs > 0 then  
               let s = trace "let xref" in
               let s = trace (string_of_int nrefs) in
               let s = trace "= salloc x" in
               let s = trace (string_of_int nrefs) in
               let _ = trace " in" in
               allocate_stack_ref (nrefs - 1)
      else
               let s = trace "\n \t" in
               s

val print_val_generic_args: (args:list argtype)-> (tag:int)->(is_sig:bool) ->ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let rec print_val_generic_args  args tag is_sig: (ST unit)
     (requires (fun _ -> True))
     (ensures (fun h0 _ h1 -> h0 == h1))= 
      let count = List.Tot.Base.length args in
      match args with
      | [] -> ()
      | hd::tl ->
           if count >= 1 then
                let _ = if is_sig then trace "(" 
                        else ()
                in
                let _ = trace "x" in
                let s = trace (string_of_int tag) in

                let _ = if not is_sig then trace " " else () in
                let _ = if is_sig then 
                           let s = trace ":" in
                           let s = print_type hd in
                           trace ")->"
                        else 
                           ()
                in print_val_generic_args tl (tag+1) is_sig
           else 
                ()
                
val print_val_generic_stackref_args: (args:list argtype)-> (tag:int)->(is_sig:bool) ->ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let rec print_val_generic_stackref_args args tag is_sig: (ST unit)
      (requires (fun _ -> True))
      (ensures (fun h0 _ h1 -> h0 == h1))= 
      let nrefs = List.Tot.Base.length args in
      match args with
       | [] -> ()
       | hd::tl  ->
          if nrefs >= 1 then
           let _ = if is_sig then trace "("
                   else ()
           in
           let _ = trace "xref" in
           let s = trace (string_of_int tag) in
           let _ = if not is_sig then trace " " else () in
           let _ = if is_sig then 
                    let s = trace ": stackref " in
                    let _ = print_type hd in
                    trace ")->"
                   else ()
           in
           print_val_generic_stackref_args tl (tag+1) is_sig
           else 
                ()

val split_list_at_4: (args:list 'a{List.Tot.Base.length args > 4}) -> ST (list 'a * list 'a)
 (requires (fun _ -> True))
 (ensures (fun h0 r h1 -> h0 == h1))
let  split_list_at_4 args = 
      let l1, h1 = (List.Tot.Base.hd args, List.Tot.Base.tail args) in
      let l2, h2 = (List.Tot.Base.hd h1, List.Tot.Base.tail h1) in
      let l3, h3 = (List.Tot.Base.hd h2, List.Tot.Base.tail h2) in
      let l4, h4 = (List.Tot.Base.hd h3, List.Tot.Base.tail h3) in
      ([l1;l2;l3;l4], h4)

let rec helper_print (d:nat) (str:string): ST unit 
 (requires (fun _ -> d >= 0))
 (ensures (fun h0 r h1 -> h0 == h1))=
  if d > 1 then
    let _ = trace str  in
    helper_print (d-1) str
  else 
    ()

let rec print_frameOf d narg is_st_ref : ST unit
 (requires (fun _ -> True))
 (ensures (fun h0 r h1 -> h0 == h1)) =
 if d > 1 then
         let _ = trace "Set.union (Set.singleton " in
         let _ = helper_print d "(frameOf sel h  " in
         let _ = if is_st_ref then 
                   trace  "xref" 
                 else trace "x" 
         in
         let _ = trace (string_of_int narg) in
         let _ = helper_print d ")" in
         let _ = trace ") " in
         print_frameOf (d-1) narg is_st_ref
 else
         (* done *)
         ()


let rec print_sel d narg is_st_ref : ST unit
 (requires (fun _ -> True))
 (ensures (fun h0 r h1 -> h0 == h1)) =
 if d > 1 then
         let _ = helper_print d "(sel h0  " in
         let _ = if is_st_ref then 
                   trace  "xref" 
                 else trace "x" 
         in
         let _ = trace (string_of_int narg) in
         helper_print d ")"


let rec print_sel_and_frame d narg is_st_ref : ST unit
 (requires (fun _ -> True))
 (ensures (fun h0 r h1 -> h0 == h1)) =
 if d > 1 then
         let _ = helper_print d "(sel h0  " in
         let _ = if is_st_ref then 
                   trace  "xref" 
                 else trace "x" 
         in
         let _ = trace (string_of_int narg) in
         let _ = helper_print d ")" in
         let _ = trace ") " in
         let _ = trace "Set.singleton " in
         let _ = helper_print d "as_addr (frameOf sel h0  " in
         let _ = if is_st_ref then 
                   trace  "xref" 
                 else trace "x" 
         in
         let _ = trace (string_of_int narg) in
         let _ = helper_print d ")" in
//         let _ = trace ") " in
         print_frameOf (d-1) narg is_st_ref
 else
         (* done *)
         ()

val get_ref_depth : argtype -> ST nat 
(requires (fun h -> True))
(ensures (fun h0 r h1 -> h0 == h1))
let rec get_ref_depth (a:argtype) = match a with
   |ABuffer a -> (get_ref_depth a) + 1
   | _ -> 0
   
val gen_generic_wrapper_sig: (fname:string) ->(args: list argtype)->(ret:argtype) -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let gen_generic_wrapper_sig (fname:string) (args: list argtype) (ret:argtype) = 
     let orignargs = List.Tot.Base.length args in
     let s = trace "(* Printing signature *)\n" in
     let s = trace "val " in
     let s = trace fname in
     let s = trace "_wrapper : " in
     let _ = if orignargs > 4 then
                 let argsl, argsh = split_list_at_4 args in 
                 let _ = print_val_generic_args argsl 1 true  in
                 (* print remaining arguments as references *)
                 print_val_generic_stackref_args argsh 1  true
               else
                 print_val_generic_args args 1 true
       in
       (* print return type *)
       let _ = trace " ST (rt: " in
       let _ = print_type ret in
       let _ = trace ")\n \t " in
       (* Print proper effect type here *)
       let _ = trace "(requires (fun h -> True  " in

       (*  local function that prints each reference is contained in memory *)
       let rec local_print_contains_clause (args: list argtype) : (ST unit)
           (requires (fun _ -> True))
           (ensures (fun h0 r h1 -> h0 == h1)) =
                     let nargs = List.Tot.Base.length args in
                     (* is this a deep pointer? *)
                     let _ = begin match args with
                             |[] -> ()
                             |hd::tl ->
                                      if (orignargs - 4 < nargs) then
                                         (* normal argument *)
                                          if (type_is_ref hd) then
                                                 let _ = trace "/\ (h `contains` x" in
                                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                                 let _ = trace ") \n\t" in
                                                 if (is_deep_ref false hd) then
                                                    let d = get_ref_depth hd in
                                                    let rec print_all_deep_refs (l:int) :ST unit
                                                      (requires (fun _ -> True))
                                                      (ensures (fun h0 r h1 -> h0 == h1)) =
                                                          if l <= d then
                                                             (* add to the modifies clause *)
                                                             let _ = trace "/\ (h `contains` "  in
                                                             let _ = print_sel l (orignargs - nargs +1) false in
                                                             let _ = trace ") \n\t" in
                                                             print_all_deep_refs (l+1)
                                                           else ()
                                                    in
                                                    let _ = print_all_deep_refs 2 in
                                                    (* continue with rest of the arguments *)
                                                    local_print_contains_clause tl
                                                 else 
                                                   (* not a deep reference - continue to rest of the arguments*)
                                                   local_print_contains_clause tl
                                           else
                                              (* not a reference - continue with rest of the arguments *)
                                              local_print_contains_clause tl
                                        
                                      else 
                                          (* stackref aguments *)
                                          let _ = trace "/\ (h `contains` xref" in 
                                          let _ = trace (string_of_int nargs) in
                                          let _ = trace ") \n\t" in
                                          if (is_deep_ref false hd) then
                                             let d = get_ref_depth hd in
                                             let rec print_all_deep_refs (l:int) :ST unit
                                               (requires (fun _ -> True))
                                               (ensures (fun h0 r h1 -> h0 == h1)) =
                                                   if l <= d then
                                                       (* add to the modifies clause *)
                                                       let _ = trace "/\ (h `contains` "  in
                                                       let _ =  print_sel l (orignargs - 4 - nargs) true in
                                                       let _ = trace ") \n\t" in
                                                       print_all_deep_refs (l+1)
                                                    else ()
                                             in
                                             let _ = print_all_deep_refs 2 in
                                             (* continue with rest of the arguments *)
                                             local_print_contains_clause tl
                                          else 
                                             (* not a deep reference - continue to rest of the arguments*)
                                             local_print_contains_clause tl
                           end 
                           (* end of match *)
                           in ()
           

       in (* end of local_print_contains_clause *)
       let _ = local_print_contains_clause args in
       let _ = trace ")) \n\t (ensures (fun h0 r h1 -> " in
       let _ = if orignargs <= 4 then 
                  trace " h0 == h1 " 
                else
                  let rec local_print_modifies_rids_clause (args:list argtype) : (ST unit)
                     (requires (fun _ -> True ))
                     (ensures (fun h0 r h1 -> h0 == h1)) =
                     let nargs = List.Tot.Base.length args in
                     (* is this a deep pointer? *)
                     let _ = begin match args with
                             |[] -> ()
                             |hd::tl ->
                                      if (orignargs - 4 < nargs) then
                                         (* normal argument *)
                                          if (type_is_ref hd) then
                                                 let _ = trace "Set.union (Set.singleton (frameOf x" in
                                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                                 let _ = trace ")) " in
                                                 if (is_deep_ref false hd) then
                                                    let d = get_ref_depth hd in
                                                    let rec print_all_deep_refs (l:int) :ST unit
                                                      (requires (fun _ -> True))
                                                      (ensures (fun h0 r h1 -> h0 == h1)) =
                                                          if l <= d then
                                                               (* add to the modifies clause *)
                                                               let _ = print_frameOf l (orignargs - nargs +1) false in
                                                               print_all_deep_refs (l+1)
                                                           else ()
                                                     in
                                                     let _ = print_all_deep_refs 2 in
                                                     (* continue with rest of the arguments *)
                                                     local_print_modifies_rids_clause tl
                                                 else 
                                                   (* not a deep reference - continue to rest of the arguments*)
                                                   local_print_modifies_rids_clause tl
                                           else
                                              (* not a reference - continue with rest of the arguments *)
                                              local_print_modifies_rids_clause tl
                                        
                                      else 
                                          (* stackref aguments *)
                                          let _ = trace "Set.union (Set.singleton (frameOf xref" in
                                          let _ = trace (string_of_int nargs) in
                                          let _ = trace ")) " in
                                          if (is_deep_ref false hd) then
                                             let d = get_ref_depth hd in
                                             let rec print_all_deep_refs (l:int) :ST unit
                                               (requires (fun _ -> True))
                                               (ensures (fun h0 r h1 -> h0 == h1)) =
                                                   if l <= d then
                                                      (* add to the modifies clause *)
                                                      let _ =  print_frameOf l (orignargs - 4 - nargs) true in
                                                      print_all_deep_refs (l+1)
                                                   else ()
                                             in
                                             let _ = print_all_deep_refs 2 in
                                             (* continue with rest of the arguments *)
                                             local_print_modifies_rids_clause tl
                                          else 
                                             (* not a deep reference - continue to rest of the arguments*)
                                             local_print_modifies_rids_clause tl
                           end 
                           (* end of function *)
                           in ()
                    in
                   let _ = trace "modifies Set.union Set.empty " in
                   let _ = local_print_modifies_rids_clause args in
                   let _  = trace "h0 h1 \n\t " in
                   let rec local_print_modifies_refs_clause (args: list argtype) : (ST unit)
                       (requires (fun _ -> True))
                       (ensures (fun h0 r h1 -> h0 == h1)) =
                     let nargs = List.Tot.Base.length args in
                     (* is this a deep pointer? *)
                     let _ = begin match args with
                             |[] -> ()
                             |hd::tl ->
                                      if (orignargs - 4 < nargs) then
                                         (* normal argument *)
                                          if (type_is_ref hd) then
                                                 let _ = trace "/\ modifies_ref (frameOf x" in
                                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                                 let _ = trace ") " in 
                                                 let _ = trace " (Set.singleton (as_addr x" in
                                                 let _ = trace (string_of_int (orignargs -nargs + 1)) in 
                                                 let _ = trace "))\n \t " in
                                                 if (is_deep_ref false hd) then
                                                    let d = get_ref_depth hd in
                                                    let rec print_all_deep_refs (l:int) :ST unit
                                                      (requires (fun _ -> True))
                                                      (ensures (fun h0 r h1 -> h0 == h1)) =
                                                          if l <= d then
                                                              let _ = trace "/\ modifies_ref (frameOf " in
                                                              (* add to the modifies_ref clause *)
                                                              let _ = print_sel_and_frame l (orignargs - nargs +1) false in
                                                              let _ = trace "\n \t " in
                                                              print_all_deep_refs (l+1)
                                                           else ()
                                                  in
                                                  let _ = print_all_deep_refs 2 in
                                                  (* continue with rest of the arguments *)
                                                  local_print_modifies_refs_clause tl
                                                 else 
                                                   (* not a deep reference - continue to rest of the arguments*)
                                                   local_print_modifies_refs_clause tl
                                           else
                                              (* not a reference - continue with rest of the arguments *)
                                              local_print_modifies_refs_clause tl
                                        
                                      else 
                                          (* stackref aguments *)
                                          let _ = trace "/\ modifies_ref (frameOf xref" in
                                          let _ = trace (string_of_int (orignargs - 4 - nargs + 1)) in
                                          let _ = trace ") " in 
                                          let _ = trace "(Set.singleton (as_addr xref" in
                                          let _ = trace (string_of_int (orignargs - 4 -nargs + 1)) in 
                                          let _ = trace ")) \n\t " in
                                          if (is_deep_ref false hd) then
                                             let d = get_ref_depth hd in
                                             let _ = trace "/\ modifies_ref (frameOf " in
                                             let rec print_all_deep_refs (l:int) :ST unit
                                               (requires (fun _ -> True))
                                               (ensures (fun h0 r h1 -> h0 == h1)) =
                                                   if l <= d then
                                                        (* add to the modifies clause *)
                                                        let _ =  print_sel_and_frame l (orignargs - 4 - nargs + 1) true in
                                                        let _ = trace ") \n \t " in
                                                        print_all_deep_refs (l+1)
                                                   else ()
                                            in
                                            let _ = print_all_deep_refs 2 in
                                            (* continue with rest of the arguments *)
                                            local_print_modifies_refs_clause tl
                                          else 
                                             (* not a deep reference - continue to rest of the arguments*)
                                             local_print_modifies_refs_clause tl
                           end 
                           (* end of function *)
                           in ()

                    (*end of function local_print_modifies_refs_clause *)
                    in
                   let _ = local_print_modifies_refs_clause args in
                   if (type_is_ref ret) then
                      (* if return type is a reference should there be a modifies clause? *)
                      trace "/\ is_eternal_region rt \n\t"
                   else
                     ()
  
       in 
       trace "))\n"
       
                                        
val gen_generic_wrapper_body: (fname:string) ->(args: list argtype)->(ret:argtype) -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let gen_generic_wrapper_body (fname:string) (args: list argtype) (ret:argtype) = 
     let orignargs = List.Tot.Base.length args in
     let s = trace "let " in
     let s = trace fname in
     let s = trace "_wrapper  " in
     let _ = if orignargs > 4 then
                 let argsl, argsh = split_list_at_4 args in 
                 let _ = print_val_generic_args argsl 1 false  in
                 (* print remaining arguments as references *)
                 print_val_generic_stackref_args argsh 1  false
               else
                 print_val_generic_args args 1 false
       in
      let _ = trace "= \n \t" in
      (* Check if bitmap is set for reference arguments *)
      let rec check_bitmap (args: list argtype) : ST unit
        (requires (fun _ -> True))
        (ensures (fun h0 r h1 -> h0 == h1)) = 
        let nargs = List.Tot.Base.length args in
         let _ =  match args with
                  |[] -> ()
                  | hd::tl -> 
                         if (orignargs - 4 < nargs) then
                            (* normal argument *)
                             if type_is_ref hd then
                                 let _ = trace "and writable (as_addr " in
                                 let _ = trace "x" in
                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                 let _ = trace ") \n \t \t" in
                                 if (is_deep_ref false hd) then
                                      let d = get_ref_depth hd in
                                      let rec print_all_deep_refs (l:int) :ST unit
                                        (requires (fun _ -> True))
                                        (ensures (fun h0 r h1 -> h0 == h1)) =
                                            if l <= d then
                                              let _ = trace "and writable (as_addr  " in
                                              (* add to the modifies_ref clause *)
                                              let _ = print_sel l (orignargs - nargs +1) false in
                                              let _ = trace ")\n \t \t" in
                                              print_all_deep_refs (l+1)
                                            else
                                              ()
                                      in
                                      let _ = print_all_deep_refs 2 in
                                      (* continue with rest of the arguments *)
                                      check_bitmap tl 
                                   else 
                                     (* not a deep reference - continue to rest of the arguments*)
                                      check_bitmap tl 
                                 
                             else
                                 (* skip the checks *)
                                 check_bitmap tl
                          else
                             if type_is_ref hd then
                                 let _ = trace "and writable (as_addr " in
                                 let _ = trace "xref" in
                                 let _ = trace (string_of_int (orignargs - 4 - nargs + 1)) in
                                 let _ = trace ") \n \t" in
                                 if (is_deep_ref false hd) then
                                      let d = get_ref_depth hd in
                                      let rec print_all_deep_refs (l:int) :ST unit
                                        (requires (fun _ -> True))
                                        (ensures (fun h0 r h1 -> h0 == h1)) =
                                            if l <= d then
                                              let _ = trace "and writable (as_addr  " in
                                              (* add to the modifies_ref clause *)
                                              let _ = print_sel l (orignargs - nargs +1) true in
                                              let _ = trace ")\n \t \t" in
                                              print_all_deep_refs (l+1)
                                            else
                                              ()
                                      in
                                      let _ = print_all_deep_refs 2 in
                                      (* continue with rest of the arguments *)
                                      check_bitmap tl 
                                   else 
                                     (* not a deep reference - continue to rest of the arguments*)
                                      check_bitmap tl 
                             else
                                 (* skip the checks *)
                                 check_bitmap tl
        in () (* end of match *)
      in (* end of check_bitmap *) 
      let _ = trace "(* check if all references and deep references are marked as wriatable in bitmap *) \n \t " in
      let _ = trace " if true   " in
      let _ = check_bitmap args in
      let _ = trace " then \n \t \t " in
      (* invoke function *)
      let s = trace "(* invoking function *)\n \t    " in
      let _ = trace "let rt = " in
      let _ = trace fname in
      let _ = trace " " in
      let _ = if orignargs > 4 then
                  let argsl, argsh = split_list_at_4 args in 
                  let _ = print_val_generic_args argsl 1 false  in
                  (* print remaining arguments as references *)
                  print_val_generic_stackref_args argsh 1  false
                else
                  print_val_generic_args args 1 false
        in
      let _ = trace " in \n \t \t rt \n \t " in
      let _ = trace "else \n \t \t (* raise an exception here? *) \n \t \t raise Halt \n" in
      ()


open FStar.List.Tot.Base

val gen_generic_wrapper: (fname:string) -> (args:list argtype)-> (ret:argtype) -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let gen_generic_wrapper (fname:string) (args:list argtype) (ret:argtype) = 
    let _ = gen_generic_wrapper_sig fname args ret in
    let _ = gen_generic_wrapper_body fname args ret in
    ()


val gen_wrapper: (f:calltable_entry)  -> ST unit
(requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let gen_wrapper (f:calltable_entry) = match f with
  | Mkcalltable_entry (fname:string) (fstart_address:nat64) (fsize:nat64) (argslist:list argtype) (ret:argtype) -> 
         gen_generic_wrapper fname argslist ret
         
(* Sample Manifest *)
val main: unit -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let main () = gen_wrapper (Mkcalltable_entry "foo" 0x1000 0x25 [ANat64; ANat64; (ABuffer (ABuffer (ABuffer ANat64))); (ABuffer (ABuffer ANat64)); (ABuffer ANat64)] (ABuffer ANat64))
           
let () = main ()
