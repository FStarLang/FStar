#light "off"
module FStar.TypeChecker.NBETerm
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env
module Z = FStar.BigInt
module C = FStar.Const


type var = bv
type sort = int

type constant =
  | Unit
  | Bool of bool
  | Int of Z.t
  | String of string * Range.range
  | Char of FStar.Char.char

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Match of t * (* the scutinee *)
             (t -> t) * (* case analysis *)
             ((t -> term) -> list<branch>)
             (* the computation that reconstructs the pattern matching, parameterized by the readback function *)
             // ZP: Keep the original branches to reconstruct just the patterns
             // NS: add a thunked pattern translations here
  | Rec of letbinding * list<letbinding> * list<t> (* Danel: This wraps a unary F* rec. def. as a thunk in F# *)
  (* Zoe : a recursive function definition together with its block of mutually recursive function definitions and its environment *)
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t) * (unit -> t) * aqual //NS: * (t * (type : unit -> t) * aqual)
  | Accu of atom * args
  (* For simplicity represent constructors with fv as in F* *)
  | Construct of fv * list<universe> * args (* Zoe: Data constructors *)
  | FV of fv * list<universe> * args (* Zoe: Free variables *)
  | Constant of constant
  | Type_t of universe
  | Univ of universe
  | Unknown (* For translating unknown types *)
  // NS:
  | Refinement of binder * t // VD: do we need to keep the aqual?
  // | Arrow of list binder * comp_t
and args = list<(t * aqual)>
//NS:
// and comp_t =
//   | Comp of lident * universes * args * flags
// and binder = ident * t //ident is just for pretty name on readback

(*
   (xi:ti) -> C uts (attributes ...)

   x:t{t}

*)

type head = t
type annot = option<t>


// Printing functions

let constant_to_string (c: constant) =
  match c with
  | Unit -> "Unit"
  | Bool b -> if b then "Bool true" else "Bool false"
  | Int i -> Z.string_of_big_int i
  | Char c -> BU.format1 "'%s'" (BU.string_of_char c)
  | String (s, _) -> BU.format1 "\"%s\"" s

let rec t_to_string (x:t) =
  match x with
  | Lam _ -> "Lam"
  | Accu (a, l) -> 
    "Accu (" ^ (atom_to_string a) ^ ") (" ^ 
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
  | Construct (fv, us, l) -> 
    "Construct (" ^ (P.fv_to_string fv) ^ ") [" ^ 
    (String.concat "; "(List.map P.univ_to_string us)) ^ "] (" ^ 
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
  | FV (fv, us, l) -> 
    "FV (" ^ (P.fv_to_string fv) ^ ") [" ^ 
    (String.concat "; "(List.map P.univ_to_string us)) ^ "] (" ^ 
    (String.concat "; " (List.map (fun x -> t_to_string (fst x)) l)) ^ ")"
  | Constant c -> constant_to_string c
  | Univ u -> "Universe " ^ (P.univ_to_string u)
  | Type_t u -> "Type_t " ^ (P.univ_to_string u)
  | Refinement ((b,_), t) -> "Refinement (" ^ (P.bv_to_string b) ^ ", " ^ (t_to_string t) ^ ")"
  | Unknown -> "Unknown"

and atom_to_string (a: atom) =
    match a with
    | Var v -> "Var " ^ (P.bv_to_string v)
    | Match (t, _, _) -> "Match " ^ (t_to_string t)
    | Rec (_,_, l) -> "Rec (" ^ (String.concat "; " (List.map t_to_string l)) ^ ")"

// NBE term manipulation 

let isAccu (trm:t) =
  match trm with
  | Accu _ -> true
  | _ -> false

let isNotAccu (x:t) =
  match x with
  | Accu (_, _) -> false
  | _ -> true


let mkConstruct i us ts = Construct(i, us, ts)
let mkFV i us ts = FV(i, us, ts)

let mkAccuVar (v:var) = Accu(Var v, [])
let mkAccuMatch (s:t) (cases: t -> t) (bs:((t -> term) -> list<branch>)) = Accu(Match (s, cases, bs), [])
let mkAccuRec (b:letbinding) (bs:list<letbinding>) (env:list<t>) = Accu(Rec(b, bs, env), [])

