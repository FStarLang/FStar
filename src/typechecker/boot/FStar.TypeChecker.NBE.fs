#light "off"
module FStar.TypeChecker.NBE
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.Syntax.Syntax

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Range = FStar.Range
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util

(* Utils *)

let map_rev (f : 'a -> 'b) (l : list<'a>) : list<'b> =
  let rec aux (l:list<'a>) (acc:list<'b>) = //NS: weird, this needs an annotation to type-check in F*; cf issue #
   match l with 
   | [] -> acc 
   | x :: xs -> aux xs (f x :: acc)
   in  aux l []

let debug_term (t : term) =
  BU.print1 "%s\n" (P.term_to_string t)

type var = bv
type sort = int

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Sort of sort (* for full CiC -- not used right now *)
  | Prod of t * t (* for full CiC -- not used right now *)
  | Match of t * (* the scutinee *)
             (t -> t) (* the closure that pattern matches the scrutiny *) 
  | FiX of (t -> t) (* Danel: This is a unary rec. def. that will not be unfolded any more *)
  | Rec of letbinding * list<t> (* Danel: This wraps a unary F* rec. def. as a thunk in F# *)
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t)
  | Fix of (t -> t) (* potentially recursive (i.e. a lambda inside ). The only difference with [Lam] is that there is an [is_accu] for the argument during application *)
  | Accu of atom * list<t>
  (* For simplicity represent constructors with fv as in F* *)
  | Construct of fv * list<t>
  | Unit
  | Bool of bool
type head = t
type annot = option<t> 

let mkConstruct i ts = Construct(i,ts)

let mkAccuVar (v:var) = Accu(Var v, [])
let mkAccuMatch (s : t) (c : t -> t) = Accu(Match (s, c), [])
let mkAccuRec (b:letbinding) (env:list<t>) = Accu(Rec(b, env), [])

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
(* Danel: app is now defined simultaneously with translate to accommodate analysing rec. defs. *)
let rec app (f:t) (x:t) =
  match f with
  | Lam f -> f x
  | Accu (a, ts) -> Accu (a, x::ts)
  | Construct (i, ts) -> Construct (i, x::ts)
  // | Rec (y, ts) -> (match x with
  //                   (* Danel: In a real F* scenario, the decreases check would happen here? *)
  //                   | Accu _ -> Accu (FiX (fun (z:t) -> translate (z::ts) y),[x])
  //                                                  (* Danel: if a rec. def. is applied 
  //                                                     to an accumulator, do not unfold 
  //                                                     it further *)
  //                   | _ -> app (translate (Rec (y, ts)::ts) y) x)
  //                                           (* Danel: if a rec. def. is applied to 
  //                                              a non-accumulator, then we unfold it *)
  | Unit
  | Bool _ -> failwith "Ill-typed application"

and translate (bs:list<t>) (e:term) : t =
    match (SS.compress e).n with
    | Tm_delayed _ -> failwith "Impossible"

    | Tm_constant (FStar.Const.Const_unit) ->
      Unit

    | Tm_constant (FStar.Const.Const_bool b) ->
      Bool b

    | Tm_bvar db -> //de Bruijn
      List.nth bs db.index

    | Tm_name x ->
      mkAccuVar x

    | Tm_abs ([x], body, _) ->
      Lam (fun (y:t) -> translate (y::bs) body)

    | Tm_fvar v ->
      mkConstruct v []
      
    | Tm_abs (x::xs, body, _) ->
      let rest = S.mk (Tm_abs(xs, body, None)) None Range.dummyRange in
      let tm = S.mk (Tm_abs([x], rest, None)) None e.pos in
      translate bs tm

    | Tm_app (e, [arg]) ->
      app (translate bs e) (translate bs (fst arg))

    | Tm_app(head, arg::args) ->
      let first = S.mk (Tm_app(head, [arg])) None Range.dummyRange in
      let tm = S.mk (Tm_app(first, args)) None e.pos in
      translate bs tm
    
    | Tm_match(scrut, branches) ->
      let rec case (scrut : t) : t = 
        match scrut with 
        | Construct(c, args) -> (* Scrutinee is a constructed value *)
          (* Assuming that all the arguments to the pattern constructors 
             are binders -- i.e. no nested patterns for now  *) 
          (* XXX : is rev needed? *)
          let branch = translate ((List.rev args) @ args) (pickBranch c branches) in
          branch
        | _ -> 
          mkAccuMatch scrut case
      in 
      case (translate bs scrut)

    | Tm_let((false, [lb]), body) -> // non-recursive let
      let def = translate bs lb.lbdef in
      translate (def::bs) body

    | Tm_let((true, [lb]), body) -> // recursive let with only one recursive definition
      let f = mkAccuRec lb bs in 
      translate (f::bs) body (* Danel: storing the rec. def. as F* code wrapped in a thunk *)

      // this will loop infinitely when the recursive argument is symbolic 
      // let def = lb.lbdef in 
      // let fnorm f = translate (f::bs) def in
      // let rec f = fnorm f in
      // translate (f::bs) body
      //failwith "Not yet implemented"
      
    | _ -> debug_term e; failwith "Not yet implemented"

and readback (x:t) : term =
    match x with
    | Unit -> S.unit_const
    | Bool true -> U.exp_true_bool
    | Bool false -> U.exp_false_bool
    | Lam f ->
      let x = S.new_bv None S.tun in
      let body = readback (f (mkAccuVar x)) in
      U.abs [S.mk_binder x] body None
    | Construct (fv, args) -> 
      let args = List.map (fun x -> as_arg (readback x)) args in
      (match args with 
       | [] -> (S.mk (Tm_fvar fv) None Range.dummyRange)
       | _ -> U.mk_app (S.mk (Tm_fvar fv) None Range.dummyRange) args)
    | Accu (Var bv, []) ->
      S.bv_to_name bv
    | Accu (Var bv, ts) ->
      let args = map_rev (fun x -> as_arg (readback x)) ts in
      U.mk_app (S.bv_to_name bv) args
    | Accu (Match (scrut, cases), ts) ->
      let args = map_rev (fun x -> as_arg (readback x)) ts in
      let head =  readback (cases scrut) in
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
       if List.exists isAccu ts then (* if there is at least one symbolic argument, do not unfold *)
         let head = 
           (* Zoe: I want the head to be [let rec f = lb in f]. Is this the right way to construct it? *)
           let f = S.new_bv None S.tun in
           S.mk (Tm_let((true, [lb]), S.bv_to_tm f)) None Range.dummyRange
         in
         let args = map_rev (fun x -> as_arg (readback x)) ts in
         (match ts with 
          | [] -> head
          | _ -> U.mk_app head args)
       else (* otherwise compute *)
         readback (curry (translate ((mkAccuRec lb bs) :: bs) lb.lbdef) ts)
    | _ -> failwith "Not yet implemented"
    
let normalize (e:term) : term = readback (translate [] e)
