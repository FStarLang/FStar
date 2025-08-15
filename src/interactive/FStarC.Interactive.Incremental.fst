(*
   Copyright 2023  Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStarC.Interactive.Incremental
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Range
open FStarC.Getopt
open FStarC.Ident
open FStarC.Errors
open FStarC.Interactive.JsonHelper
open FStarC.Interactive.QueryHelper
open FStarC.Interactive.PushHelper
open FStarC.Universal
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Interactive
open FStarC.Parser.ParseIt
open FStarC.Interactive.Ide.Types
module P = FStarC.Parser.ParseIt
module BU = FStarC.Util
open FStarC.Parser.AST
open FStarC.Parser.AST.Util
open FStarC.Parser.AST.Diff { eq_decl }
open FStarC.Class.Show

let qid = string & int
let qst a = qid -> a & qid
let return (x:'a) : qst 'a = fun q -> x, q
let (let!) (f:qst 'a) (g: 'a -> qst 'b)
  : qst 'b
  = fun q -> let x, q' = f q in
          g x q'

let run_qst (f:qst 'a) (q:string)
  : 'a
  = fst (f (q, 0))


let rec map (f:'a -> qst 'b) (l:list 'a)
  : qst (list 'b)
  = match l with
    | [] -> return []
    | hd::tl ->
      let! hd = f hd in
      let! tl = map f tl in
      return (hd :: tl)
  
let shift_qid (q:qid) (i:int) = fst q, snd q + i

let next_qid
  : qst qid
  = fun q -> let q = shift_qid q 1 in
          q, q

let get_qid
  : qst qid
  = fun q -> q, q

let as_query (q:query') 
  : qst query
  = let! (qid_prefix, i) = next_qid in
    return 
      {
        qq=q;
        qid=qid_prefix ^ "." ^ show i
      }

(* This function dumps a symbol table for the decl that has just been checked *)
let dump_symbols_for_lid (l:lident)
: qst query
= let r = Ident.range_of_lid l in
  let start_pos = Range.start_of_range r in
  let end_pos = Range.end_of_range r in
  let start_line = Range.line_of_pos start_pos in
  let start_col = Range.col_of_pos start_pos in
  let end_line = Range.line_of_pos end_pos in
  let end_col = Range.col_of_pos end_pos in
  let position = "<input>", start_line, start_col in
  as_query (Lookup(Ident.string_of_lid l,
                    LKCode,
                    Some position,
                    ["type"; "documentation"; "defined-at"],
                    Some (JsonAssoc [("fname", JsonStr "<input>");
                                    ("beg", JsonList [JsonInt start_line; JsonInt start_col]);
                                    ("end", JsonList [JsonInt end_line; JsonInt end_col])])))

let dump_symbols (d:decl)
: qst (list query)
= let open FStarC.Parser.AST in
  let ls = lidents_of_decl d in
  map dump_symbols_for_lid ls


(* Push a decl for checking, and before it runs,
   print a progress message "fragment-started"
   for the decl that is about to run *)
let push_decl (push_kind:push_kind)
              (with_symbols:bool)
              (write_full_buffer_fragment_progress: fragment_progress -> unit)
              (ds:decl & code_fragment)              
  : qst (list query)
  = let open FStarC.Range in
    let d, s = ds in
    let pq = {
        push_kind;
        push_line = line_of_pos (start_of_range d.drange);
        push_column = col_of_pos (start_of_range d.drange);
        push_peek_only = false;
        push_code_or_decl = Inr ds
    } in
    let progress st =
      write_full_buffer_fragment_progress (FragmentStarted d);
      (QueryOK, []), Inl st
    in
    let! cb = as_query (Callback progress) in
    let! push = as_query (Push pq) in
    if with_symbols
    then (
      let! lookups = dump_symbols d in
      return ([cb; push] @ lookups)
    )
    else (
      return [cb; push]
    )
    
let push_decls (push_kind:push_kind)
               (with_symbols:bool)
               (write_full_buffer_fragment_progress : fragment_progress -> unit)
               (ds:list (decl & code_fragment))
  : qst (list query)
  = let! qs = map (push_decl push_kind with_symbols write_full_buffer_fragment_progress) ds in
    return (List.flatten qs)
  
let pop_entries (e:list repl_stack_entry_t)
  : qst (list query)
  = map (fun _ -> as_query Pop) e
  
let repl_task (_, (p, _)) = p

let push_kind_geq pk1 pk2 =
  pk1=pk2 || (
  match pk1, pk2 with
  | FullCheck, LaxCheck -> true
  | LaxCheck, SyntaxCheck -> true
  | _ -> false
  )
(* Find a prefix of the repl stack that matche a prefix of the decls ds, 
   pop the rest of the stack
   and push the remaining suffix of decls
*)
let inspect_repl_stack (s:repl_stack_t)
                       (ds:list (decl & code_fragment))
                       (push_kind : push_kind)
                       (with_symbols:bool)
                       (write_full_buffer_fragment_progress: fragment_progress -> unit)                       
  : qst (list query & list json)
  = let entries = List.rev s in
    let push_decls = push_decls push_kind with_symbols write_full_buffer_fragment_progress in
    match BU.prefix_until 
             (function (_, (PushFragment _, _)) -> true | _ -> false)
             entries          
    with
    | None ->
      let! ds = push_decls ds in
      return (ds, [])
    
    | Some (prefix, first_push, rest) ->
      let entries = first_push :: rest in
      let repl_task (_, (p, _)) = p in
      let rec matching_prefix (accum:list json) (lookups:list query) entries (ds:list (decl & code_fragment))
        : qst (list query & list json)
        = match entries, ds with
          | [], [] ->
            return (lookups, accum)
            
          | e::entries, d::ds -> (
            match repl_task e with
            | Noop -> 
              matching_prefix accum lookups entries (d::ds)
            | PushFragment (Inl frag, _, _) ->
              let! pops = pop_entries (e::entries) in
              let! pushes = push_decls (d::ds) in
              return (lookups @ pops @ pushes, accum)
            | PushFragment (Inr d', pk, issues) ->
              if eq_decl (fst d) d' && pk `push_kind_geq` push_kind
              then (
                let d, s = d in
                write_full_buffer_fragment_progress (FragmentSuccess (d, s, pk));
                if with_symbols
                then let! lookups' = dump_symbols d in
                     matching_prefix (issues@accum) (lookups'@lookups) entries ds
                else
                    matching_prefix (issues@accum) lookups entries ds
              )
              else let! pops = pop_entries (e::entries) in
                   let! pushes = push_decls (d::ds) in
                   return (pops @ lookups @ pushes, accum)
            )

         | [], ds ->
           let! pushes = push_decls ds in
           return (lookups@pushes, accum)

         | es, [] ->
           let! pops = pop_entries es in
           return (lookups@pops, accum)
      in
      matching_prefix [] [] entries ds 

(* A reload_deps request just pops away the entire stack of PushFragments.
   We also push on just the `module A` declaration after popping. That's done below. *)
let reload_deps repl_stack =
  let pop_until_deps entries
  : qst (list query)
  = match BU.prefix_until
            (fun e -> match repl_task e with
                      | PushFragment _ | Noop -> false
                      | _ -> true)
            entries
    with
    | None -> return []
    | Some (prefix, _, _) ->
      let! pop = as_query Pop in
      return (List.map (fun _ -> pop) prefix)
  in
  pop_until_deps repl_stack

(* A utility to parse a chunk, used both in full_buffer and formatting *)
let parse_code lang (code:string) =
    P.parse lang (Incremental { 
                         frag_fname = Range.file_of_range initial_range;
                         frag_text = code;
                         frag_line = Range.line_of_pos (Range.start_of_range initial_range);
                         frag_col = Range.col_of_pos (Range.start_of_range initial_range);
                })
    
(* Format FStarC.Errors.error into a JSON error message *)
let syntax_issue (raw_error, msg, range) =
    let _, _, num = FStarC.Errors.lookup raw_error in
    let issue = { 
        issue_msg = msg;
        issue_level = EError;
        issue_range = Some range;
        issue_number = Some num;
        issue_ctx = []
    } in
    issue

(* See comment in the interface file *)
let run_full_buffer (st:repl_state)
                    (qid:string)
                    (code:string)
                    (request_type:full_buffer_request_kind)
                    (with_symbols:bool)
                    (write_full_buffer_fragment_progress: fragment_progress -> unit)
  : list query & list json
  = let parse_result = parse_code None code in
    let log_syntax_issues err =
      match err with
      | None -> ()
      | Some err ->
        let issue = syntax_issue err in
        write_full_buffer_fragment_progress (FragmentError [issue])
    in
    let filter_decls decls =
      match request_type with
      | VerifyToPosition (_, line, _col)
      | LaxToPosition (_, line, _col) ->
        List.filter
          (fun (d, _) ->
            let start = Range.start_of_range d.drange in
            let start_line = Range.line_of_pos start in
            start_line <= line)
          decls
      | _ -> decls
    in
    let qs = 
      match parse_result with
      | IncrementalFragment (decls, _, err_opt) -> (
        // This is a diagnostic message that is send to the IDE as an info message
        // The script test-incremental.py in tests/ide/ depends on this message
        Format.print1 "Parsed %s declarations\n" (show (List.length decls));
        match request_type, decls with
        | ReloadDeps, d::_ ->
          run_qst (let! queries = reload_deps (!repl_stack) in
                   let! push_mod = push_decl FullCheck with_symbols write_full_buffer_fragment_progress d in
                   return (queries @ push_mod, []))
                  qid

        | _ ->
          let decls = filter_decls decls in
          let push_kind = 
            match request_type with
            | LaxToPosition _ -> LaxCheck
            | Lax -> LaxCheck
            | _ -> FullCheck
          in
          let queries, issues = 
              run_qst (inspect_repl_stack (!repl_stack) decls push_kind with_symbols write_full_buffer_fragment_progress) qid
          in
          if request_type <> Cache then log_syntax_issues err_opt;
          if Debug.any()
          then (
            Format.print1 "Generating queries\n%s\n" 
                      (String.concat "\n" (List.map query_to_string queries))
          );
          if request_type <> Cache then (queries, issues) else ([] , issues)

      )
        
      | ParseError err ->
        if request_type = Full then log_syntax_issues (Some err);
        [], []
      | _ -> 
        failwith "Unexpected parse result"
    in
    qs

(* See comment in interface file *)
let format_code (st:repl_state) (code:string)
  = let maybe_lang =
      match st.repl_lang with
      | [] -> None
      | {d=FStarC.Parser.AST.UseLangDecls l}::_ -> Some l
    in
    let parse_result = parse_code maybe_lang code in
    match parse_result with
    | IncrementalFragment (decls, comments, None) ->
      let doc_to_string doc =
          FStarC.Pprint.pretty_string (Util.float_of_string "1.0") 100 doc
      in
      let formatted_code_rev, leftover_comments =
        List.fold_left
          (fun (out, comments) (d, _) -> 
            let doc, comments = FStarC.Parser.ToDocument.decl_with_comments_to_document d comments in
            doc_to_string doc::out, comments)
          ([], List.rev comments)
          decls
      in
      let code = formatted_code_rev |> List.rev  |> String.concat "\n\n" in
      let formatted_code =
        match leftover_comments with
        | [] -> code
        | _ ->
          let doc = FStarC.Parser.ToDocument.comments_to_document leftover_comments in
          code ^ "\n\n" ^ doc_to_string doc
      in
      Inl formatted_code
    | IncrementalFragment (_, _, Some err) ->
      Inr [syntax_issue err]
    | ParseError err ->
      Inr [syntax_issue err]
    | _ ->
      failwith "Unexpected parse result"
