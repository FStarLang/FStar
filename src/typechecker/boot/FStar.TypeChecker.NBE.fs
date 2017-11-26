#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.Syntax.Syntax
open FStar.Ident
  
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Range = FStar.Range
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env


(* Utils *)

// VD: This seems necessary for the OCaml build
let max a b = if a > b then a else b

let map_rev (f : 'a -> 'b) (l : list<'a>) : list<'b> =
  let rec aux (l:list<'a>) (acc:list<'b>) = //NS: weird, this needs an annotation to type-check in F*; cf issue #
   match l with 
   | [] -> acc 
   | x :: xs -> aux xs (f x :: acc)
   in  aux l []

let debug_term (t : term) =
  BU.print1 "%s\n" (P.term_to_string t)

let debug_sigmap (m : BU.smap<sigelt>) =
  BU.smap_fold m (fun k v u -> BU.print2 "%s -> %%s\n" k (P.sigelt_to_string_short v)) ()

type var = bv
type sort = int

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Type of universe (* Zoe: Not sure why this needs to be an atom, just following the paper *)
  | Match of t * (* the scutinee *)
             (t -> t) (* the closure that pattern matches the scrutiny *) 
  | Rec of letbinding * list<t> (* Danel: This wraps a unary F* rec. def. as a thunk in F# *)
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t)
  | Accu of atom * list<t>
  (* For simplicity represent constructors with fv as in F* *)
  | Construct of fv * list<t> (* Zoe: This is used for both type and data constructors*)
  | Unit
  | Bool of bool
type head = t
type annot = option<t> 

let is_not_accu (x:t) =
  match x with
  | Accu (_, _) -> false
  | _ -> true

let mkConstruct i ts = Construct(i,ts)

let mkAccuVar (v:var) = Accu(Var v, [])
let mkAccuMatch (s : t) (c : t -> t) = Accu(Match (s, c), [])
let mkAccuRec (b:letbinding) (env:list<t>) = Accu(Rec(b, env), [])
let mkAccTyp (u:universe) = Accu(Type u, [])

let isAccu (trm:t) = 
  match trm with 
  | Accu _ -> true
  | _ -> false
  
let rec pickBranch (c : fv) (branches : list<branch>) : term = 
  match branches with
  | [] -> failwith "Branch not found"
  | ({v = Pat_cons (c', args)}, _, e) :: bs when (fv_eq c c') ->
    e
  | b :: bs -> pickBranch c bs

(* Tests is the application is full and if none of the arguments is symbolic *)
let rec test_args ts cnt = 
  match ts with 
  | [] -> cnt <= 0 
  | t :: ts -> (not (isAccu t)) && test_args ts (cnt - 1)

(* Count the number of abstractions in the body of a let rec. 
   It accounts for abstractions instantiated inside the body.
   This analysis needs further refinement, for example see the let in case. 
*)
let rec count_abstractions (t : term) : int =
    match (SS.compress t).n with
    | Tm_delayed _ | Tm_unknown -> failwith "Impossible" 
    | Tm_uinst _
    | Tm_bvar _ 
    | Tm_name _
    | Tm_fvar _
    | Tm_constant _ 
    | Tm_type _ 
    | Tm_arrow _ 
    | Tm_uvar _ 
    | Tm_refine _
    | Tm_unknown -> 0
   
    
    | Tm_abs (xs, body, _) ->
      List.length xs + count_abstractions body

    | Tm_app(head, args) -> 
      max (count_abstractions head - List.length args) 0
    
    | Tm_match(scrut, branches) ->
      (match branches with
       | [] -> failwith "Branch not found"
       (* count just one branch assuming it is well-typed *)
       | (_, _, e) :: bs -> count_abstractions e)

    | Tm_let (_, t) 
      (* This is not quite right. We need to somehow cound the abstractions of the let definition
         as it might be used in head position. For instance we might have something like [let t = e in t]
       *)
    | Tm_meta (t, _) 
    | Tm_ascribed (t, _, _) -> count_abstractions t
        

(* XXX unused *)
let rec mkBranches branches cont = 
  match branches with 
  | ({ v = (Pat_cons (fv, pats))}, _, _) :: branches' -> 
    (* a new binder for each argument *)
    let (args, binders) = 
      List.fold_right
        (fun (p : pat * bool) ((args:list<t>), (bs:list<(pat * bool)>)) ->
           let x = S.new_bv None S.tun in 
           (mkAccuVar x :: args, (S.withinfo (Pat_var x) Range.dummyRange, snd p) :: bs)
        ) pats ([], []) in
    let value = Construct (fv, args) in
    let pat = S.withinfo (Pat_cons (fv, binders)) Range.dummyRange  in
    let branch = (pat, None, cont value) in
    branch :: mkBranches branches' cont
  | _ -> failwith "Unexpected pattern" 

(* We are not targeting tagless normalization at this point *)
let rec app (f:t) (x:t) =
  match f with
  | Lam f -> f x
  | Accu (a, ts) -> Accu (a, x::ts)
  | Construct (i, ts) -> Construct (i, x::ts)
  | Unit
  | Bool _ -> failwith "Ill-typed application"

and iapp (f:t) (args:list<t>) = 
  match args with
  | [] -> f
  | _ -> iapp (app f (List.hd args)) (List.tl args)

and translate (env:Env.env) (bs:list<t>) (e:term) : t =
    match (SS.compress e).n with
    | Tm_delayed _ -> failwith "Tm_delayed: Impossible"
      
    | Tm_unknown _ -> failwith "Tm_unknown: Impossible"
      
    | Tm_constant (FStar.Const.Const_unit) ->
      Unit

    | Tm_constant (FStar.Const.Const_bool b) ->
      Bool b

    | Tm_constant c -> 
      let err = "Tm_constant " ^ (P.const_to_string c) ^ ": Not yet implemented" in
      debug_term e; failwith err
      
    | Tm_bvar db -> //de Bruijn
      List.nth bs db.index

    | Tm_uinst _ -> debug_term e; failwith "Tm_uinst: Not yet implemented"

    | Tm_type u -> mkAccTyp u

    | Tm_arrow (bs, c) -> debug_term e; failwith "Tm_arrow: Not yet implemented"

    | Tm_refine _ -> debug_term e; failwith "Tm_refine: Not yet implemented"

    | Tm_ascribed _ -> debug_term e; failwith "Tm_ascribed: Not yet implemented"

    | Tm_uvar _ -> debug_term e; failwith "Tm_uvar: Not yet implemented"
    
    | Tm_meta (e, _) -> translate env bs e
    
    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([x], body, _) ->
      Lam (fun (y:t) -> translate env (y::bs) body)

    | Tm_fvar fvar ->
      let find_in_sigtab (env : Env.env) (lid : lident) : option<sigelt> = BU.smap_try_find env.sigtab (text_of_lid lid) in
      (match find_in_sigtab env fvar.fv_name.v with 
       | Some { sigel = Sig_let ((is_rec, [lb]), _) n} ->
         if is_rec then 
           mkAccuRec lb [] 
         else 
           translate env [] lb.lbdef
       | None -> mkConstruct fvar [] (* Zoe : Treat all other cases as type/data constructors for now. *)
         (* Zoe : Z and S dataconstructors from the examples are not in the environment *) 
       )
    | Tm_abs (x::xs, body, _) ->
      let rest = S.mk (Tm_abs(xs, body, None)) None Range.dummyRange in
      let tm = S.mk (Tm_abs([x], rest, None)) None e.pos in
      translate env bs tm

    | Tm_app (e, [arg]) ->
      app (translate env bs e) (translate env bs (fst arg))

    | Tm_app(head, arg::args) ->
      let first = S.mk (Tm_app(head, [arg])) None Range.dummyRange in
      let tm = S.mk (Tm_app(first, args)) None e.pos in
      translate env bs tm
    
    | Tm_match(scrut, branches) ->
      let rec case (scrut : t) : t = 
        match scrut with 
        | Construct(c, args) -> (* Scrutinee is a constructed value *)
          (* Assuming that all the arguments to the pattern constructors 
             are binders -- i.e. no nested patterns for now  *) 
          (* XXX : is rev needed? *)
          let branch = translate env ((List.rev args) @ bs) (pickBranch c branches) in
          branch
        | _ -> 
          mkAccuMatch scrut case
      in 
      case (translate env bs scrut)

    | Tm_let((false, [lb]), body) -> // non-recursive let
      let def = translate env bs lb.lbdef in
      translate env (def::bs) body

    | Tm_let((true, [lb]), body) -> // recursive let with only one recursive definition
      let f = mkAccuRec lb bs in 
      translate env (f::bs) body (* Danel: storing the rec. def. as F* code wrapped in a thunk *)

      // this will loop infinitely when the recursive argument is symbolic 
      // let def = lb.lbdef in 
      // let fnorm f = translate (f::bs) def in
      // let rec f = fnorm f in
      // translate (f::bs) body
      //failwith "Not yet implemented"
      
(* [readback] creates named binders and not De Bruijn *)
and readback (env:Env.env) (x:t) : term =
    match x with
    | Unit -> S.unit_const
    
    | Bool true -> U.exp_true_bool
    | Bool false -> U.exp_false_bool
    
    | Lam f ->
      let x = S.new_bv None S.tun in
      let body = readback env (f (mkAccuVar x)) in
      U.abs [S.mk_binder x] body None
    
    | Construct (fv, args) -> 
      let args = List.map (fun x -> as_arg (readback env x)) args in
      (match args with 
       | [] -> (S.mk (Tm_fvar fv) None Range.dummyRange)
       | _ -> U.mk_app (S.mk (Tm_fvar fv) None Range.dummyRange) args)
      
    | Accu (Var bv, []) ->
      S.bv_to_name bv
    | Accu (Var bv, ts) ->
      let args = map_rev (fun x -> as_arg (readback env x)) ts in
      U.mk_app (S.bv_to_name bv) args
    
    | Accu (Type u, []) ->
      S.mk (Tm_type u) None Range.dummyRange
    | Accu (Type u, ts) ->
      let args = map_rev (fun x -> as_arg (readback env x)) ts in
      U.mk_app (S.mk (Tm_type u) None Range.dummyRange) args
               
    | Accu (Match (scrut, cases), ts) ->
      let args = map_rev (fun x -> as_arg (readback env x)) ts in
      let head =  readback env (cases scrut) in
      (match ts with 
       | [] -> head
       | _ -> U.mk_app head args)
   
    | Accu (Rec(lb, bs), ts) ->
       let rec curry hd args = 
       match args with 
       | [] -> hd
       | [arg] -> app hd arg
       | arg :: args -> app (curry hd args) arg
       in
       let args_no = count_abstractions lb.lbdef in 
       // Printf.printf "Args no. %d\n" args_no;
       if test_args ts args_no then (* if the arguments are not symbolic and the application is not partial compute *)
         readback env (curry (translate env ((mkAccuRec lb bs) :: bs) lb.lbdef) ts)
       else (* otherwise do not unfold *)
         let head = 
           (* Zoe: I want the head to be [let rec f = lb in f]. Is this the right way to construct it? *)
           let f = match lb.lbname with
                   | BU.Inl bv -> S.bv_to_name bv
                   | BU.Inr fv -> failwith "Not yet implemented"
           in
           S.mk (Tm_let((true, [lb]), f)) None Range.dummyRange
         in
         let args = map_rev (fun x -> as_arg (readback env x)) ts in
         (match ts with 
          | [] -> head
          | _ -> U.mk_app head args)
      
// Zoe: Commenting out conflict with Danel
// =======
//     | Accu (Rec (lb, bs), ts) -> 
//        (match (SS.compress lb.lbdef).n with
//         | Tm_abs (args, _, _) -> 
//             if (List.length ts = List.length args &&
//                 List.fold_right (fun x y -> x && y) (List.map is_not_accu ts) true)
//             then readback (iapp (translate ((Accu (Rec (lb, bs), []))::bs) lb.lbdef) ts)
//             else (let args = List.map (fun x -> as_arg (readback x)) ts in
//                   let body = (match args with 
//                               | [] -> (match lb.lbname with
//                                        | BU.Inl bv -> S.bv_to_name bv
//                                        | BU.Inr fv -> failwith "Not yet implemented")
//                               | _  -> (match lb.lbname with
//                                        | BU.Inl bv -> U.mk_app (S.bv_to_name bv) args
//                                        | BU.Inr fv -> failwith "Not yet implemented")) in 
//                   S.mk (Tm_let((true, [lb]), body)) None Range.dummyRange)
//                   (* Currently not normalizing the let-bound definition on its own, 
//                      only normalizing it when it is unfolded *)
//         | _ -> failwith "Recursive definition not a function")
// >>>>>>> 86f93ae6edc257258f376954fed7fba11f53ff83

let normalize (env : Env.env) (e:term) : term = 
  //debug_sigmap env.sigtab;
  readback env (translate env [] e)
