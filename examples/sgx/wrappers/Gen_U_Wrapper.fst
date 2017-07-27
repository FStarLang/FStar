module Gen_U_Wrapper

(* Generate Wrappers *)
open WrapperUtil
open Manifest
open FStar.IO
open FStar.HyperStack.ST

val gen_generic_wrapper_sig: (fname:string) ->(args: list argtype)->(ret:argtype) -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let gen_generic_wrapper_sig (fname:string) (args: list argtype) (ret:argtype) = 
     let orignargs = List.Tot.Base.length args in
     let s = trace "\n (* Printing signature for U's function wrapper. \n * V's code invokes U's function " in
     let _ = trace fname in
     let _ = trace " using the wrapper " in
     let _ = trace fname in
     let _ = trace "_wrapper \n *)\n" in
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
       let _ = trace " Stack (rt: " in
       let _ = print_type ret in
       let _ = trace ")\n \t " in
       (* Print proper effect type here *)
       let _ = trace "(requires (fun h0 -> True  " in

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
                                                 let _ = trace "/\ (h0 `contains` x" in
                                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                                 let _ = trace ") \n\t" in
                                                 let _ = trace "/\ (not is_code_reference x" in
                                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                                 let _ = trace ") \n\t" in
                                                 if (is_deep_ref false hd) then
                                                    let d = get_ref_depth hd in
                                                    let rec print_all_deep_refs (l:int) :ST unit
                                                      (requires (fun _ -> True))
                                                      (ensures (fun h0 r h1 -> h0 == h1)) =
                                                          if l <= d then
                                                             (* add to the modifies clause *)
                                                             let _ = trace "/\ (h0 `contains` "  in
                                                             let _ = print_sel l (orignargs - nargs +1) false in
                                                             let _ = trace ") \n\t" in
                                                             let _ = trace "/\ (not is_code_reference " in
                                                             let _ = print_sel l (orignargs -nargs +1 ) false in 
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
                                          let _ = trace "/\ (h0 `contains` xref" in 
                                          let _ = trace (string_of_int nargs) in
                                          let _ = trace ") \n\t" in
                                          let _ = trace "/\ (not is_code_reference xref" in
                                          let _ = trace (string_of_int nargs) in
                                          let _ = trace ") \n\t" in
                                          if (is_deep_ref false hd) then
                                             let d = get_ref_depth hd in
                                             let rec print_all_deep_refs (l:int) :ST unit
                                               (requires (fun _ -> True))
                                               (ensures (fun h0 r h1 -> h0 == h1)) =
                                                   if l <= d then
                                                       (* add to the modifies clause *)
                                                       let _ = trace "/\ (h0 `contains` "  in
                                                       let _ =  print_sel l (orignargs - 4 - nargs) true in
                                                       let _ = trace ") \n\t" in
                                                       let _ = trace "/\ (not is_code_reference " in
                                                       let _ = print_sel l (orignargs - 4 - nargs) true in 
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
                  (* FIXME: Not right. Check for references *)
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
                   let _ = trace " u_mem " in
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
                   let _ = if (type_is_ref ret) then
                              (* if return type is a reference should there be a modifies clause? *)
                              trace "/\ (not is_vheap_reference rt) \n\t"
                           else
                             ()
                   in
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
      let _ = trace "\n \t" in
      let _ = trace "(* Clearing bitmap *) \n \t" in
      let _ = trace "let _ = clear_bitmap in \n \t" in
      let _ = trace "(* Setting the mutability bit of references for arguments *)\n \t" in 
      let rec set_bitmap (args: list argtype) : ST unit
        (requires (fun _ -> True))
        (ensures (fun h0 r h1 -> h0 == h1)) = 
        let nargs = List.Tot.Base.length args in
         let _ =  match args with
                  |[] -> ()
                  | hd::tl -> 
                         if (orignargs - 4 < nargs) then
                            (* normal argument *)
                             if type_is_ref hd then
                                 let _ = trace "if (is_stack_reference " in
                                 let _ = trace "x" in
                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                 let _ = trace ") then \n \t \t" in
                                 let _ = trace "set_ref_as_mutable x" in
                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                 let _ = trace "\n \t " in
                                 if (is_deep_ref false hd) then
                                      let d = get_ref_depth hd in
                                      let rec print_all_deep_refs (l:int) :ST unit
                                        (requires (fun _ -> True))
                                        (ensures (fun h0 r h1 -> h0 == h1)) =
                                            if l <= d then
                                              let _ = trace "if (is_stack_reference " in
                                              let _ = print_sel l (orignargs - nargs +1) false in
                                              let _ = trace ") then \n \t \t" in
                                              let _ = trace "set_ref_as_mutable x" in
                                              let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                              let _ = trace "\n \t " in
                                              print_all_deep_refs (l+1)
                                            else
                                              ()
                                      in
                                      let _ = print_all_deep_refs 2 in
                                      (* continue with rest of the arguments *)
                                      set_bitmap tl 
                                   else 
                                     (* not a deep reference - continue to rest of the arguments*)
                                      set_bitmap tl 
                                 
                             else
                                 (* skip the checks *)
                                 set_bitmap tl
                          else
                             if type_is_ref hd then
                                 let _ = trace "if (is_stack_reference  " in
                                 let _ = trace "xref" in
                                 let _ = trace (string_of_int (orignargs - 4 - nargs + 1)) in
                                 let _ = trace ") then \n \t \t" in
                                 let _ = trace "set_ref_as_mutable xref" in
                                 let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                 let _ = trace "\n \t " in
                                 
                                 if (is_deep_ref false hd) then
                                      let d = get_ref_depth hd in
                                      let rec print_all_deep_refs (l:int) :ST unit
                                        (requires (fun _ -> True))
                                        (ensures (fun h0 r h1 -> h0 == h1)) =
                                            if l <= d then
                                              let _ = trace "if (is_stack_reference " in
                                              let _ = print_sel l (orignargs - 4 - nargs +1) true in
                                              let _ = trace ") then \n \t \t" in
                                              let _ = trace "set_ref_as_mutable xref" in
                                              let _ = trace (string_of_int (orignargs - nargs + 1)) in
                                              let _ = trace "\n \t " in
                                              print_all_deep_refs (l+1)
                                            else
                                              ()
                                      in
                                      let _ = print_all_deep_refs 2 in
                                      (* continue with rest of the arguments *)
                                      set_bitmap tl 
                                   else 
                                     (* not a deep reference - continue to rest of the arguments*)
                                      set_bitmap tl 
                             else
                                 (* skip the checks *)
                                 set_bitmap tl
        in () (* end of match *)
      in (* end of check_bitmap *) 
      let _ = set_bitmap args in
      let _ = trace "(* invoking function *)\n \t" in
      let _ = trace "let rt = " in
      (* invoke function *)
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
       let _ = trace "\n \t in rt \n" in
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


val gen_manifest_helper_routines : unit -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 r h1 -> h0 == h1))
let gen_manifest_helper_routines () = 
 let _ = trace " (* These should be part of FStar.HyperStack.ST.fst *) \n" in
 let _ = trace "assume val set_ref_as_mutable: (addr:stackref 'a) -> (rt:stackref 'a{rt.is_mutable = true}) \n" in
 let _ = trace "assume val unset_ref_as_mutable: (addr:stackref 'a) -> (rt:stackref 'a{rt.is_mutable = false}) \n" in
 let _ = trace "assume val is_ref_mutable: (addr: stackref 'a) -> bool \n\n" in
 let _ = trace "assume val is_stack_reference: (addr: reference 'a) -> bool \n" in
 let _ = trace "assume val is_uheap_reference: (addr: reference 'a) -> bool \n" in
 let _ = trace "assume val is_vheap_reference : (addr: referece 'a) -> bool \n" in
 let _ = trace "assume val is_code_reference: (addr:reference 'a) -> bool \n\n" in
 let _ = trace "val get_stack_frames_below : (h:mem) -> (list rid) \n" in
 let _ = trace "(* Not quite right - IN PROGRESS *) \n" in
 let _ = trace "let get_stack_frames_below h = \n" in
 let _ = trace "    let top = h.tip \n" in
 let _ = trace "    let rec get_last_parent (f:rid) (l:list rid) = \n" in
 let _ = trace "         let p = HH.parent f in \n " in
 let _ = trace "         if p = HH.root then l else get_last_parent p::l \n \n" in
 let _ = trace "assume val refs_in_region: (l:list rid)->(list reference) \n\n" in
 let _ = trace "val get_all_refs_from_stack_frames_below : (h:mem) -> (list reference) \n" in
 let _ = trace "let get_all_refs_from_stack_frames_below h = \n" in
 let _ = trace "    let sframes = get_stack_frames_below h \n" in
 let _ = trace "    refs_in_region sframes \n\n" in
 let _ = trace "assume val get_bitmap_unset_references : (h:mem)->(list reference) \n \n" in
 let _ = trace "let clear_bitmap = \n " in
 let _ = trace "\t let h = get () \n " in
 let _ = trace "\t let lr = get_all_refs_from_stack_frames_below h \n" in
 let _ = trace "\t let rec clear_each_ref_mutability = function \n" in
 let _ = trace "\t \t [] -> () \n " in
 let _ = trace "\t \t|hd::tl -> let _ = unset_ref_as_mutable hd in \n " in
 let _ = trace "\t \t                clear_each_ref_mutability tl \n" in
 ()

let print_icon () = 
 let _ = trace "module U_Manifest\n" in
 let _ = trace "open Manifest \n" in
 trace " \n \n (* Automatically generated wrappers for U  \n * DO NOT MODIFY  \n *) \n \n"
 
(* Sample Manifest *)
val main: unit -> ST unit
(requires (fun _ -> True))
(ensures (fun h0 _ h1 -> h0 == h1))
let main () = 
   let _ = print_icon () in
   let _ = gen_manifest_helper_routines () in
   gen_wrapper (Mkcalltable_entry "ufunc" 0x1000 0x25 [ANat64; ANat64; (ABuffer (ABuffer (ABuffer ANat64))); (ABuffer (ABuffer ANat64)); (ABuffer ANat64)] (ABuffer ANat64))
           
let () = main ()

