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

module FStar.Interactive.Incremental
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Compiler.Range
open FStar.Compiler.Util
open FStar.Getopt
open FStar.Ident
open FStar.Errors
open FStar.Interactive.JsonHelper
open FStar.Interactive.QueryHelper
open FStar.Interactive.PushHelper
open FStar.Universal
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Interactive
open FStar.Parser.ParseIt
module SS = FStar.Syntax.Syntax
module DsEnv = FStar.Syntax.DsEnv
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable
open FStar.Interactive.Ide.Types
open FStar.Interactive.ReplState
module P = FStar.Parser.ParseIt
module BU = FStar.Compiler.Util
open FStar.Parser.AST
open FStar.Parser.AST.Comparison

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
        qid=qid_prefix ^ "." ^ string_of_int i
      }

let push_decl (d:decl)
  : qst query
  = let open FStar.Compiler.Range in
    let pq = {
        push_kind = FullCheck;
        push_line = line_of_pos (start_of_range d.drange);
        push_column = col_of_pos (start_of_range d.drange);
        push_peek_only = false;
        push_code_or_decl = Inr d
    } in
    as_query (Push pq)
    
let push_decls (ds:list decl)
  : qst (list query)
  = map push_decl ds
  
let pop_entries (e:list repl_stack_entry_t)
  : qst (list query)
  = map (fun _ -> as_query Pop) e
  
let response_success (d:decl)
  : qst json
  = let! (q, _) = get_qid in
    let contents = JsonAssoc (["ranges", json_of_def_range d.drange]) in
    return (JsonAssoc [("kind", JsonStr "response");
                       ("query-id", JsonStr q);
                       ("status", JsonStr "success");
                       ("contents", contents)])
  
let inspect_repl_stack (s:repl_stack_t)
                       (ds:list decl)
                       (write_full_buffer_fragment_progress: either decl (list issue) -> unit)                       
  : qst (list query) // & list json)
  = let entries = List.rev s in
    match BU.prefix_until 
             (function (_, (PushFragment _, _)) -> true | _ -> false)
             entries          
    with
    | None ->
      let! ds = push_decls ds in
      return ds
    
    | Some (prefix, first_push, rest) ->
      let entries = first_push :: rest in
      let repl_task (_, (p, _)) = p in
      let rec matching_prefix entries ds
        : qst (list query)
        = match entries, ds with
          | [], [] ->
            return []
            
          | e::entries, d::ds -> (
            match repl_task e with
            | Noop -> 
              matching_prefix entries (d::ds)
            | PushFragment (Inl frag) ->
              let! pops = pop_entries  (e::entries) in
              let! pushes = push_decls (d::ds) in
              return (pops @ pushes)
            | PushFragment (Inr d') ->
              if eq_decl d d'
              then (
                write_full_buffer_fragment_progress (Inl d);
                matching_prefix entries ds
              )
              else let! pops = pop_entries (e::entries) in
                   let! pushes = push_decls (d::ds) in
                   return (pops @ pushes)
            )

         | [], ds ->
           let! pushes = push_decls ds in
           return pushes

         | es, [] ->
           let! pops = pop_entries es in
           return pops
      in
      matching_prefix entries ds 
      
let run_full_buffer (st:repl_state)
                    (qid:string)
                    (code:string)
                    (write_full_buffer_fragment_progress: either decl (list issue) -> unit)
  : list query
  = let parse_result = 
        P.parse (Incremental { 
                         frag_fname = Range.file_of_range initial_range;
                         frag_text = code;
                         frag_line = Range.line_of_pos (Range.start_of_range initial_range);
                         frag_col = Range.col_of_pos (Range.start_of_range initial_range);
                })
    in
    let log_syntax_issues err =
      match err with
      | None -> ()
      | Some (raw_error, msg, range) ->
        let _, _, num = FStar.Errors.lookup raw_error in
        let issue = { 
            issue_msg = msg;
            issue_level = EError;
            issue_range = Some range;
            issue_number = Some num;
            issue_ctx = []
        } in
        write_full_buffer_fragment_progress (Inr [issue])
    in
    let qs = 
      match parse_result with
      | IncrementalFragment (decls, _, err_opt) ->
        let queries = 
            run_qst (inspect_repl_stack (!repl_stack) decls write_full_buffer_fragment_progress) qid
        in
        log_syntax_issues err_opt;
        if Options.debug_any()
        then (
          BU.print1 "Generating queries\n%s\n" 
                    (String.concat "\n" (List.map query_to_string queries))
        );
        queries
        
      | ParseError err ->
        log_syntax_issues (Some err);
        []
      | _ -> 
        failwith "Unexpected parse result"
    in
    qs
