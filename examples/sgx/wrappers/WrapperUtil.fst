module WrapperUtil

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
