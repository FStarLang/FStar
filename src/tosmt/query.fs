(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
 
module Microsoft.FStar.Z3Encoding.Query

open Microsoft.FStar
open Z3Encoding.Env
open Z3Encoding.BasicDT
open Microsoft.Z3
open Util
open Absyn
open Term
open Profiling 
open DecodeTyp
open EncodingDT

let log = logopt
let flush = function None -> () | Some (s:System.IO.StreamWriter) -> s.Flush()
let close = function None -> () | Some (s:System.IO.StreamWriter) -> s.Close()
let logOps z3 = function None -> fun _ _ -> () | Some s -> logOps z3 s
let cleanup tc = 
  (* let _ = pr "Cleaning up Z3 context\n" in  *)
    tc.z3ctx.Dispose(); 
    close tc.stream

let logEval opstate tm = 
    if !Options.logQueries then 
      let z3 = opstate.termctx.z3ctx in 
      let stream = opstate.termctx.stream in
      let ppmap = opstate.st.pp_name_map in 
        (log stream "(check-sat)\n";
         log stream ";; (get-model)\n";
         log stream (spr "(eval %s)\n" (termToSmt (init_info z3 ppmap) tm));
         flush stream)
    else ()
      
let push opstate = 
  if !Options.z3exe then ()
  else (ignore(opstate.termctx.z3solver.Push());
        if !Options.logQueries then (log opstate.termctx.stream "\n(push)\n"))
    
let pop opstate = 
  if !Options.z3exe then ()
  else (ignore(opstate.termctx.z3solver.Pop()); 
        if !Options.logQueries then (log opstate.termctx.stream "\n(pop)\n"))

let new_scope ctx f = 
  let _ = push ctx in 
  let result = f () in 
  let _ = pop ctx in 
    result
      
let giveZ3 opstack opstate theory = 
  let z3 = opstate.termctx.z3ctx in 
  let stream = opstate.termctx.stream in
  let ppmap = opstate.st.pp_name_map in 
    logOps z3 stream ppmap theory;
    flush stream;
    opsToZ3 opstate.termctx theory;
    opstack@theory
        
let z3ctr = ref 1

let echo ctx msg = 
  if !Options.logQueries then 
    let msg = (spr "%s-%d" msg !z3ctr) in 
      (* pr "%s\n" msg; *)
      ignore <| giveZ3 [] ctx [Echo msg]
  else ()
      
let askZ3 ctx q hdl = 
  incr z3ctr;
  let z3 = ctx.termctx.z3ctx, ctx.termctx.z3solver in 
  let labels = ctx.st.labels in
  let info = init_info (fst z3) ctx.st.pp_name_map in 
    (try 
       if !Options.logQueries then 
         (log ctx.termctx.stream (opToSmt info (Assume(q, None, AName "Query")));
          log ctx.termctx.stream "\n(check-sat)\n";
          flush ctx.termctx.stream);
       hdl (processZ3Answer ctx.termctx.stream labels z3 (termToZ3Term ctx.termctx q)) info
     with 
         :? ZZZError -> handleZ3Error q)

let tryZ3Unsat ctx q = askZ3 ctx q (fun b _ -> b)

let tryZ3UnsatWithQops ctx qops q = 
  if (echo ctx "Qfree"; tryZ3Unsat ctx q)
  then true
  else (match qops with 
          | [] -> false
          | _ -> new_scope ctx (fun () -> 
                                  ignore <| giveZ3 [] ctx qops;
                                  echo ctx "Quants";
                                  tryZ3Unsat ctx q))
    
let insistZ3Unsat range ctx qops q = 
  if (echo ctx "Qfree"; tryZ3Unsat ctx q)
  then true
  else (match qops with 
          | [] -> false
          | _ -> new_scope ctx (fun () ->
                                  ignore <| giveZ3 [] ctx qops; 
                                  echo ctx "Quants";
                                  askZ3 ctx q (fun b info ->
                                                 if not b 
                                                 then raise (Error(spr "Failed to prove verification condition: %s\n" (termToSmt info q), range))
                                                 else b)))
    
let instantiateUvar opstate tm t =
  match findOpt (fun (_, tm', _) -> termEq tm tm') opstate.st.uvars with
    | None ->
        let uvars = String.concat "; " (List.map (fun ((uv,k), tm, _) -> spr "'U%d <-> %A" (Unionfind.uvar_id uv) tm) opstate.st.uvars) in
          raise (Err(spr "Failed to resolve unification variable corresponding to %A; only have [%s]" tm uvars))
    | Some ((uv,k), _, _) ->
        let _ = pr "Instantiating uvar %d\n" (Unionfind.uvar_id uv) in
          match Tcutil.check_unify (uv,k) t with
            | None -> twithsort (Typ_uvar(uv,k)) k
            | Some msg -> raise (Error(spr "%s\n Current environement:%A\n" msg (opstate.st.env), t.p))

let tag_res_free tm =  
  let rec tag_res_free tm = 
    let aux tl mk = 
      let tl, b = List.fold_left (fun (out,b) t -> let t,b' = tag_res_free t in t::out, b&&b') ([],true) tl in
        if b 
        then 
          let t = mk (List.map (function {tm=ResFree t} -> t | _ -> raise Impos) (List.rev tl)) in
            ResFree t, b
        else mk (List.rev tl), b in
      match tm.tm with
        | Residue _ -> tm, false
        | Funsym _
        | True
        | False
        | Integer _
        | BoundV  _
        | FreeV   _ 
        | ConstArray _ 
        | LT  _
        | LTE _
        | GT _
        | GTE _
        | Add _
        | Sub _
        | Div _
        | Mul _
        | Mod _
        | Minus _
        | Z3Term _ -> ResFree tm, true
        | PP(a, b) -> aux [a;b] (fun [a;b] -> PP(a,b))
        | App(f, s, terms) -> 
            aux (List.ofArray terms) (fun tl -> App(f, s, Array.ofList tl))
        | Forall(pats, sorts, names, t) -> 
            aux [t] (fun [t] -> Forall(pats, sorts, names, t))
        | Exists(pats, sorts, names, t) -> 
            aux [t] (fun [t] -> Exists(pats, sorts, names, t))
        | Not t -> 
            aux [t] (fun [t] -> Not t)
        | Cases terms -> aux terms Cases 
        | And(t1,t2) -> aux [t1;t2] (fun [t1;t2] -> And(t1,t2))
        | Or(t1,t2) -> aux [t1;t2] (fun [t1;t2] -> Or(t1,t2))
        | Imp(t1,t2) -> aux [t1;t2] (fun [t1;t2] -> Imp(t1,t2))
        | Iff(t1,t2) -> aux [t1;t2] (fun [t1;t2] -> Iff(t1,t2))
        | Eq(t1,t2) ->  aux [t1;t2] (fun [t1;t2] -> Eq(t1,t2))
        | LT(t1,t2) ->  aux [t1;t2] (fun [t1;t2] -> LT(t1,t2))
        | LTE(t1,t2) ->  aux [t1;t2] (fun [t1;t2] -> LTE(t1,t2))
        | GT(t1,t2)  ->  aux [t1;t2] (fun [t1;t2] -> GT(t1,t2))
        | GTE(t1,t2) ->  aux [t1;t2] (fun [t1;t2] -> GTE(t1,t2))
        | Select(t1,t2) -> aux [t1;t2] (fun [t1;t2] -> Select(t1,t2))
        | IfThenElse(t1,t2,t3,topt) -> aux [t1;t2;t3] (fun [t1;t2;t3] -> IfThenElse(t1,t2,t3,topt))
        | Update(t1,t2,t3) -> aux [t1;t2;t3] (fun [t1;t2;t3] -> Update(t1,t2,t3))
        | Hole _ 
        | Function _ 
        | Application _ -> pr "Unexpected term in tag_res_free %A\n" tm; raise Impos in 
    (* let tm = normalizeTerm tm in  *)
    (* pr "Normalized query term is %s\n" (tm.ToString()); *)
    tag_res_free tm

let hasQops opstate = match opstate.st.qops with 
  | [] -> false
  | _ -> true


let resolve range opstate (MkResidue(tm, guessOpt, builder)) =
  let z3 = opstate.termctx.z3ctx in 
  let z3solver = opstate.termctx.z3solver in 
  let giveZ3 t = ignore (giveZ3 [] opstate t) in
  let insistZ3Unsat = insistZ3Unsat range opstate in 
  let tryZ3Unsat = tryZ3Unsat opstate in
  let tryZ3UnsatWithQops = tryZ3UnsatWithQops opstate in
  let echo = echo opstate in
  let new_scope f = new_scope opstate f in
  let logEval = logEval opstate in
  let log msg = log opstate.termctx.stream msg in
  let fail () = raise (Error(spr "Z3 says unknown: Failed to resolve existential variable %A" tm, range)) in
  let decode res = 
    let t = decodeTyp opstate.termctx ([], opstate) res in
    let uv = instantiateUvar opstate tm t in
    (* let _ = pr "Decoded %s to %s\n" (z3.ToString(res)) (uv.ToString()) in *)
      Some (runState opstate (builder [] res)) in
  let rec evalAndDecode retry =
    if retry then (echo "Qfree model"; incr z3ctr) else echo "Model with quants";
    logEval tm;
    let mutable model = null in
      match z3solver.Check() with 
        | Status.UNSATISFIABLE -> (* Z3 says unsat ... so unreachable branch *) None 
        | Status.SATISFIABLE
        | Status.UNKNOWN -> 
            (try
               let res = (try
                            if z3solver.Model = null then fail ()
                            else z3solver.Model.Eval(termToZ3Term opstate.termctx tm)
                          with :? Z3Exception -> fail()) in 
               let _ = new_scope (fun () -> 
                                    if retry then echo "Qfree" else echo "Quants";
                                    if not (tryZ3Unsat (Not(Eq(tm, withSort Type_sort <| Z3Term(res))))) then raise (Decoding_failure(4, res)) else ()) in 
               let  _ = if !Options.silent then () else pr "(%d) Evaluated %A to %s\n" !z3ctr tm (res.ToString()) in
                 decode res
             with Decoding_failure(ix,tm) -> 
               if retry && hasQops opstate 
               then new_scope (fun () -> 
                                 log ";;Retrying\n";
                                 giveZ3 (List.rev opstate.st.qops); 
                                 evalAndDecode false)
               else (raise (Error(spr "(%d) Failed to decode type: %s" ix (tm.ToString()), range)))) in
    match guessOpt with 
      | None -> evalAndDecode true 
      | Some ({tm=App(_, _, [| guessedStr |])}) ->
          (* let _ = pr "Processing guess: %A\n" guessedStr in *)
          let finder (o:op) : option<tm> = match o with
            | (Assume({tm=Forall(_, _, _, {tm=Imp(_, {tm=Imp(_, rhs)})})}, _, AName "assumption::Term_fvar_Prims.IsElt_typing")) ->
                let conjs = flatten_and rhs in
                  (* pr "Found a matching qop names with %d conjuncts\n" (List.length conjs); *)
                let finder2 (e:tm) : option<tm> = 
                  (* let _ = pr "Trying to match conjunct .\n"  in *)
                  match e.tm with 
                    | (Eq({tm=App("GetType", _,
                                  [| {tm=IfThenElse(_, _, _, Some ({tm=App("Select", _, [| _; _; str |])}))} |])},
                          {tm=App("Typ_app", _,
                                  [| _; guess|])})) when termEq str guessedStr -> Some guess
                    | _ -> None in 
                  Util.find_map conjs finder2 
            | _ -> None in 
          let guess = Util.find_map opstate.st.qops finder  in
            match guess with 
              | None -> evalAndDecode true
              | Some res -> 
                  (* pr "Guessed %A resolved to %A\n" guessedStr res;  *)
                  if new_scope (fun () -> tryZ3UnsatWithQops opstate.st.qops (Not(Eq(tm, res)))) 
                  then (try decode (termToZ3Term opstate.termctx res) 
                        with Decoding_failure _ -> evalAndDecode true) (* guess is no good! *)
                  else evalAndDecode true
  
let processQuery range opstack mkTctx opstate (query:tm) : bool = 
  let shadowCtr = ref 0 in 
  let insistZ3Unsat = insistZ3Unsat range in
  let query,is_res_free = tag_res_free query in 
  (* let _ = pr "************Query is res_free? %A****************\n" is_res_free in  *)
  let rec aux opstack tm opstate : bool * opState =
    match tm.tm with
      | ResFree tm ->
          if is_res_free
          then insistZ3Unsat opstate opstate.st.qops (Not tm), opstate
          else new_scope opstate (fun () -> insistZ3Unsat opstate opstate.st.qops (Not tm)), opstate
            
      | Forall(_, sorts, names, body) -> 
          let namesl = List.ofArray names in 
          let sortsl = List.ofArray sorts in 
          let newnames, tms = List.unzip <| List.map2 (fun (xbvd, xref) sort -> 
                                                         let y,xstr = match xbvd with
                                                           | Inl x -> genident (Some(range_of_bvd x)), (string_of_bvd x)
                                                           | Inr x -> genident (Some(range_of_bvd x)), (string_of_bvd x) in
                                                         let tm = FreeV(y.idText, sort) in 
                                                           match !xref with 
                                                             | Some tm -> pr "Quant %s already bound to %s\n" xstr (tm.ToString()); raise Impos
                                                             | _ -> 
                                                                 (* pr "Binding quant %s to %s\n" xstr (tm.ToString());  *)
                                                                 xref := Some tm; 
                                                                 (xbvd, xref), tm) 
              namesl sortsl in 
          let ops = List.map (function ({tm=FreeV(nm,sort)}) -> DeclFun(nm, [||], sort, None)) tms in
            new_scope opstate (fun () -> 
                                 let opstack = giveZ3 opstack opstate ops in 
                                 let _, opstate = addOps ops opstate in 
                                   aux opstack body opstate)
              
      | Imp(t1, t2) ->
          new_scope opstate (fun () -> 
                               let opstack = giveZ3 opstack opstate [Assume(t1, None, AName "")] in 
                                 fst (aux opstack t2 opstate)), opstate
            
      | Cases tms -> 
          if not !Options.parallel then
            tms |> List.forall (fun tm -> new_scope opstate (fun () -> 
                                                               fst (aux opstack tm opstate))), opstate
          else
            (pr "(%d) Spawning %d threads\n" !z3ctr (List.length tms);
            (Seq.ofList tms
            |> Seq.mapi (fun i tm ->
                           async {
                             if i > 0 then 
                               let tctx, _ = mkTctx None in
                               let opstate = {opstate with termctx=tctx} in
                                 ignore <| giveZ3 [] opstate opstack;
                                 let result = fst (aux opstack tm opstate) in 
                                   cleanup tctx;
                                   return result
                             else
                               return fst (aux opstack tm opstate)
                           })
            |> Async.Parallel
            |> Async.RunSynchronously
            |> Array.forall (fun b -> b)), opstate)
              
      | And(q1, q2) -> 
          let b1, st = aux opstack q1 opstate in 
            if b1 then aux opstack q2 opstate
            else false, opstate
              
      | Residue (guard, residue) -> 
          let opstack = giveZ3 opstack opstate [Assume(guard, None, AName "")] in 
          let res = new_scope opstate (fun () -> resolve range opstate residue) in 
            (match res with 
               | Some (((moreops, query), opstate)) -> 
                   let opstack = giveZ3 opstack opstate (List.rev moreops) in
                     aux opstack (fst <| tag_res_free query) opstate
               | None -> true, opstate)
              
      | _ -> new_scope opstate (fun () -> insistZ3Unsat opstate opstate.st.qops (Not tm)), opstate 
          
  and aux_shadow opstack tm opstate = 
    if not !Options.parallel 
    then aux opstack tm opstate
    else
      (incr shadowCtr;
       pr "Moving to a shadow context\n";
       let tctx, _ = mkTctx (Some (string_of_int !shadowCtr)) in 
       let opstate = {opstate with termctx=tctx} in
         ignore <| giveZ3 [] opstate opstack;
         aux opstack tm opstate)
  in 
    fst (aux opstack query opstate)
      
(* ******************************************************************************** *)
(* External interface *)
(* ******************************************************************************** *)

let cache tns dcs opstate phi =
  let os = System.IO.File.OpenWrite ("query.cache") in
  let formatter = new System.Runtime.Serialization.Formatters.Binary.BinaryFormatter() in
    formatter.Serialize(os,box ([(tns, dcs, opstate.st, phi)]));
    os.Flush(); os.Close()

//let restore () = 
//  let is = System.IO.File.OpenRead ("query.cache") in
//  let formatter = new System.Runtime.Serialization.Formatters.Binary.BinaryFormatter() in
//  let res = formatter.Deserialize(is) in
//  let result = match ((Microsoft.FSharp.Core.Operators.unbox res) : 'a list) with 
//    | [(tns, dcs, st, phi)] -> 
//        let z3 = mkZ3() in 
//        let tctx, _ = mkTermctx z3 tns dcs in 
//        let ops = {termctx=tctx; st=st} in 
//          pr "Encoding query formula\n";
//          let query, queryOps = "encodeQueryFormula" ^^ lazy runState ops (encodeFormula' phi) in
//            pr "Done encoding\n";
//    | _ -> failwith "deserialization failed: expected one item" in
//    is.Close(); result
      
let query' (env:Tcenv.env) (phi:formula) : bool =
  let init, mkTctx = initState env in 
  (* let _ =  pr "About to encode environment\n" in *)
  let _, envops = "encodeEnvironment" ^^ lazy (runState init encodeEnvironment) in 
  let bgtheory = List.rev envops.st.ops in
  (* let _ =  pr "About to give Z3 bg theory\n" in *)
  let _ = giveZ3 [] envops bgtheory in 
  (* let _ =  pr "Gave Z3 BG theory\n" in *)
    let _ = 
      if !Options.logQueries 
      then logopt init.termctx.stream ";; Starting queries\n" in
    let envops = {envops with st={envops.st with ops=Mark (Inr 0)::envops.st.ops}; strip_labels=false} in
      (* pr "Encoding query formula %s\n" (phi.ToString()); *)
      (* pr "Encoding query formula %A\n" phi; *)
    let query, qstate = "encodeQueryFormula" ^^ lazy runState envops (encodeQuery phi) in 
    let queryOps, _ = takeUntil (function (Mark (Inr 0)) -> true | _ -> false) qstate.st.ops in 
      (* pr "Done encoding to %s\n" (query.ToString()); *)
      if !Options.__unsafe 
      then ((* pr "Finished!\n";  *)true)
      else
        let opstack = giveZ3 bgtheory envops (List.rev queryOps) in 
          (* pr "About to process query\n"; *)
          let res = processQuery phi.p opstack mkTctx qstate query in 
            cleanup envops.termctx;
            res

let query env phi = 
  Encoding.check_skip 
    (fun () -> 
       pr "%s\n" (Range.string_of_range (Tcenv.get_range env));
       pr "%s\n" (Pretty.strTypAsFormula phi))
    (fun () -> query' env phi)
    
let mkEq (env:Tcenv.env) (t:typ) (e1:exp) (e2:exp) : typ =
  let eq_k = Tcenv.lookup_typ_lid env Const.eq_lid in
  let eq_typ = twithsort (Typ_const((fvwithsort Const.eq_lid eq_k), None)) eq_k in
  let eq_app1_k = open_kind eq_k t in
  let eq_app1 = twithinfo (Typ_app(eq_typ, t)) eq_app1_k eq_typ.p in
  let eq_app2_k = open_kind_with_exp eq_app1.sort e1 in
  let eq_app2 = twithinfo (Typ_dep(eq_app1, e1)) eq_app2_k e1.p in
  let eq_app3_k = open_kind_with_exp eq_app2.sort e2 in
  let eq_app3 = twithinfo (Typ_dep(eq_app2, e2)) eq_app3_k e2.p in
    eq_app3

let query_equality (env:Tcenv.env) (e1:Absyn.exp) (e2:Absyn.exp) : bool =
  let phi = mkEq env e1.sort e1 e2 in 
    query env phi
