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
open FStar.Char
open FStar.String

module PC = FStar.Parser.Const
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env
module Z = FStar.BigInt
module C = FStar.Const
module Range = FStar.Range


type var = bv
type sort = int

type constant =
  | Unit
  | Bool of bool
  | Int of Z.t
  | String of string * Range.range
  | Char of FStar.Char.char
  | Range of Range.range

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
  | Lam of (list<t> -> t) * list<(unit -> arg)> * int  // Zoe : body * args * arrity
  | Accu of atom * args
  (* For simplicity represent constructors with fv as in F* *)
  | Construct of fv * list<universe> * args (* Zoe: Data constructors *)
  | FV of fv * list<universe> * args (* Zoe: Free variables *)
  | Constant of constant
  | Type_t of universe
  | Univ of universe
  | Unknown (* For translating unknown types *)
  | Arrow of (list<t> -> t) * list<(unit -> arg)>
  // Refinement of binder * t // VD: do we need to keep the aqual?
  // | Arrow of list binder * comp_t
and arg = t * aqual
and args = list<arg>
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
  | Range r -> BU.format1 "Range %s" (Range.string_of_range r)

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
  | Arrow _ -> "Arrow" // TODO : revisit
//  | Refinement ((b,_), t) -> "Refinement (" ^ (P.bv_to_string b) ^ ", " ^ (t_to_string t) ^ ")"
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

// Embedding and de-embedding


type embedding<'a> = {
  em  : 'a -> t;
  un  : t -> option<'a>;
  typ : t;
}

let embed (e:embedding<'a>) (x:'a) : t = e.em x
let unembed (e:embedding<'a>) (trm:t) : option<'a> = e.un trm
let type_of (e:embedding<'a>) : t = e.typ

let mk_emb em un typ = {em = em; un = un; typ = typ}

let lid_as_constr (l:lident) (us:list<universe>) (args:args) : t =
    mkConstruct (lid_as_fv l S.delta_constant (Some Data_ctor)) us args

let lid_as_typ (l:lident) (us:list<universe>) (args:args) : t =
    mkConstruct (lid_as_fv l S.delta_constant None) us args

let as_iarg (a:t) : arg = (a, Some S.imp_tag)
let as_arg (a:t) : arg = (a, None)

//  Non-dependent arrow
let make_arrow1 t1 (a:arg) : t = Arrow ((fun _ -> t1), [(fun _ -> a)])

// Emdebbing at abstract types
let e_any : embedding<t> =
    let em = (fun a -> a) in
    let un =  (fun t -> Some t) in
    mk_emb em un (lid_as_typ PC.term_lid [] [])

// Emdebbing at type unit
let e_unit : embedding<unit> =
    let em a = Constant Unit in
    let un t = Some () in // No runtime typecheck here
    mk_emb em un (lid_as_typ PC.unit_lid [] [])

// Embeddind at type bool
let e_bool : embedding<bool> =
    let em a = Constant (Bool a) in
    let un t =
      match t with
      | Constant (Bool a) -> Some a
      | _ -> None
    in
    mk_emb em un (lid_as_typ PC.bool_lid [] [])

// Embeddind at type char
let e_char : embedding<char> =
    let em c = Constant (Char c) in
    let un c =
      match c with
      | Constant (Char a) -> Some a
      | _ -> None
    in
    mk_emb em un (lid_as_typ PC.char_lid [] [])

// Embeddind at type string
let e_string : embedding<string> =
  let em s = Constant (String (s, Range.dummyRange)) in
  let un s =
    match s with
    | Constant (String (s, _)) -> Some s
    | _ -> None
  in
  mk_emb em un (lid_as_typ PC.string_lid [] [])

// Embeddind at type int
let e_int : embedding<Z.t> =
    let em c = Constant (Int c) in
    let un c =
        match c with
        | Constant (Int a) -> Some a
        | _ -> None
    in
    mk_emb em un (lid_as_typ PC.int_lid [] [])

// Embedding at option type
let e_option (ea : embedding<'a>) =
    let em (o:option<'a>) : t =
        match o with
        | None ->
          lid_as_constr PC.none_lid [U_zero] [as_iarg (type_of ea)]
        | Some x ->
          lid_as_constr PC.some_lid [U_zero] [as_iarg (type_of ea);
                                              as_arg (embed ea x)]
    in
    let un (trm:t) : option<option<'a>> =
        match trm with
        | Construct (fvar, us, args) when S.fv_eq_lid fvar PC.none_lid ->
          Some None
        | Construct (fvar, us, [_; (a, _)]) when S.fv_eq_lid fvar PC.some_lid ->
          BU.bind_opt (unembed ea a) (fun a -> Some (Some a))
        | _ -> None
    in
    mk_emb em un (lid_as_typ PC.option_lid [U_zero] [as_arg (type_of ea)])


// Emdedding tuples
let e_tuple2 (ea:embedding<'a>) (eb:embedding<'b>) =
    let em (x:'a * 'b) : t =
        lid_as_constr (PC.lid_Mktuple2)
                      [U_zero;U_zero]
                      [as_iarg (type_of ea);
                       as_iarg (type_of eb);
                       as_arg (embed ea (fst x));
                       as_arg (embed eb (snd x))]
    in
    let un (trm:t) : option<('a * 'b)> =
        match trm with
        | Construct (fvar, us, [_; _; (a, _); (b, _)]) when S.fv_eq_lid fvar PC.lid_Mktuple2 ->
          BU.bind_opt (unembed ea a) (fun a ->
          BU.bind_opt (unembed eb b) (fun b ->
          Some (a, b)))
        | _ -> None
    in
    mk_emb em un (lid_as_typ PC.lid_tuple2 [U_zero] [as_arg (type_of ea);
                                                     as_arg (type_of eb)])

// Embeddind range
let e_range : embedding<Range.range> =
    let em r = Constant (Range r) in
    let un t =
    match t with
    | Constant (Range r) -> Some r
    | _ -> None
    in
    mk_emb em un (lid_as_typ PC.range_lid [] [])

// Emdedding lists
let e_list (ea:embedding<'a>) =
    let em (l:list<'a>) : t =
        let typ = as_iarg (type_of ea) in
        let nil = lid_as_constr PC.nil_lid [U_zero] [typ] in
        let cons hd tl = lid_as_constr PC.cons_lid [U_zero] [typ; as_arg (embed ea hd); as_arg tl] in
        List.fold_right cons l nil
    in
    let rec un (trm:t) : option<list<'a>> =
        match trm with
        | Construct (fv, _, _) when S.fv_eq_lid fv PC.nil_lid -> Some []
        | Construct (fv, _, [(_, Some (Implicit _)); (hd, None); (tl, None)])
          // Zoe: Not sure why this case is need; following Emdeddings.fs
        | Construct (fv, _, [(hd, None); (tl, None)])
            when S.fv_eq_lid fv PC.cons_lid ->
          BU.bind_opt (unembed ea hd) (fun hd ->
          BU.bind_opt (un tl) (fun tl ->
          Some (hd :: tl)))
        | _ -> None
    in
    mk_emb em un (lid_as_typ PC.list_lid [U_zero] [as_arg (type_of ea)])


let e_arrow1 (ea:embedding<'a>) (eb:embedding<'b>) =
    let em (f : 'a -> 'b) : t = Lam((fun tas -> match unembed ea (List.hd tas) with
                                          | Some a -> embed eb (f a)
                                          | None -> failwith "cannot unembed function argument"),
                                 [fun _ -> as_arg (type_of eb)], 1)
    in
    let un (lam : t) : option<('a -> 'b)> =
        match lam with
        | Lam (ft, _, _) -> Some (fun (x:'a) -> match unembed eb (ft [embed ea x]) with 
                                           | Some x -> x
                                           | None -> failwith "cannot unembed function result")
        | _ -> None
    in
    mk_emb em un (make_arrow1 (type_of ea) (as_iarg (type_of eb)))

(* Interface for building primitive steps *)

let arg_as_int    (a:arg) = fst a |> unembed e_int

let arg_as_bool   (a:arg) = fst a |> unembed e_bool

let arg_as_char   (a:arg) = fst a |> unembed e_char 

let arg_as_string (a:arg) = fst a |> unembed e_string 

let arg_as_list   (e:embedding<'a>) (a:arg) = fst a |> unembed (e_list e)

let arg_as_bounded_int ((a, _) : arg) : option<(fv * Z.t)> =
    match a with
    | FV (fv1, [], [(Constant (Int i), _)])
      when BU.ends_with (Ident.text_of_lid fv1.fv_name.v) 
                        "int_to_t" ->
      Some (fv1, i) 
    | _ -> None

let int_as_bounded int_to_t n =
    let c = embed e_int n in
    let int_to_t args = FV(int_to_t, [], args) in
    int_to_t [as_arg c]


(* XXX a lot of code duplication. Same code as in cfg.fs *)
let lift_unary (f : 'a -> 'b) (aopts : list<option<'a>>) : option<'b> =
        match aopts with
        | [Some a] -> Some (f a)
        | _ -> None


let lift_binary (f : 'a -> 'a -> 'b) (aopts : list<option<'a>>) : option<'b> =
        match aopts with
        | [Some a0; Some a1] -> Some (f a0 a1)
        | _ -> None

let unary_op (as_a : arg -> option<'a>) (f : 'a -> t) (args : args) : option<t> =
    lift_unary f (List.map as_a args)

let binary_op (as_a : arg -> option<'a>) (f : 'a -> 'a -> t) (args : args) : option<t> =
    lift_binary f (List.map as_a args)

let unary_int_op (f:Z.t -> Z.t) =
    unary_op arg_as_int (fun x -> embed e_int (f x))
    
let binary_int_op (f:Z.t -> Z.t -> Z.t) =
    binary_op arg_as_int (fun x y -> embed e_int (f x y))

let unary_bool_op (f:bool -> bool) =
    unary_op arg_as_bool (fun x -> embed e_bool (f x))

let binary_bool_op (f:bool -> bool -> bool) =
    binary_op arg_as_bool (fun x y -> embed e_bool (f x y))

let binary_string_op (f : string -> string -> string) =
    binary_op arg_as_string (fun x y -> embed e_string (f x y))

let mixed_binary_op (as_a : arg -> option<'a>) (as_b : arg -> option<'b>)
       (embed_c : 'c -> t) (f : 'a -> 'b -> 'c) (args : args) : option<t> =
             match args with
             | [a;b] ->
                begin
                match as_a a, as_b b with
                | Some a, Some b -> Some (embed_c (f a b))
                | _ -> None
                end
             | _ -> None

let list_of_string' (s:string) : t =
  embed (e_list e_char) (list_of_string s)
  // let name l = mk (Tm_fvar (lid_as_fv l delta_constant None)) rng in
  // let char_t = name PC.char_lid in
  // let charterm c = mk (Tm_constant (Const_char c)) rng in
  // U.mk_list char_t rng <| List.map charterm (list_of_string s)

let string_of_list' (l:list<char>) : t =
    let s = string_of_list l in
    Constant (String (s, Range.dummyRange))

let string_compare' (s1:string) (s2:string) : t =
    let r = String.compare s1 s2 in
    embed e_int (Z.big_int_of_string (BU.string_of_int r))


let string_concat' args : option<t> =
    match args with
    | [a1; a2] ->
        begin match arg_as_string a1 with
        | Some s1 ->
            begin match arg_as_list e_string a2 with
            | Some s2 ->
                let r = String.concat s1 s2 in
                Some (embed e_string r)
            | _ -> None
            end
        | _ -> None
        end
    | _ -> None

let string_of_int (i:Z.t) : t =
    embed e_string (Z.string_of_big_int i)

let string_of_bool (b:bool) : t =
    embed e_string (if b then "true" else "false")

let decidable_eq (neg:bool) (args:args) : option<t> =
    match args with
    | [(_typ, _); (a1, _); (a2, _)] -> failwith "decidable_eq not yet implemented"
    | _ -> failwith "Unexpected number of arguments"

let interp_prop (args:args) : option<t> =
    match args with
    | [(_typ, _); (a1, _); (a2, _)]    //eq2
    | [(_typ, _); _; (a1, _); (a2, _)] ->    //eq3
      failwith "propositional equality not yet implemented"
      // (match U.eq_tm a1 a2 with
      //  | U.Equal -> Some ({U.t_true with pos=r})
      //  | U.NotEqual -> Some ({U.t_false with pos=r})
      //  | _ -> None)
   | _ -> failwith "Unexpected number of arguments"

let dummy_interp (lid : Ident.lid) (args : args) : option<t> = 
    failwith ("No interpretation for " ^ (Ident.string_of_lid lid))


let prims_to_fstar_range_step (args:args) : option<t> =
    match args with
    | [(a1, _)] ->
      begin match unembed e_range a1 with
      | Some r -> Some (embed e_range r)
      | None -> None
      end
   | _ -> failwith "Unexpected number of arguments"


let string_split' args : option<t> =
    match args with
    | [a1; a2] ->
        begin match arg_as_list e_char a1 with
        | Some s1 ->
            begin match arg_as_string a2 with
            | Some s2 ->
                let r = String.split s1 s2 in
                Some (embed (e_list e_string) r)
            | _ -> None
            end
        | _ -> None
        end
    | _ -> None


let string_substring' args : option<t> =
  match args with
  | [a1; a2; a3] ->
      begin match arg_as_string a1, arg_as_int a2, arg_as_int a3 with
      | Some s1, Some n1, Some n2 ->
        let n1 = Z.to_int_fs n1 in
        let n2 = Z.to_int_fs n2 in
        begin
        try let r = String.substring s1 n1 n2 in
            Some (embed e_string r)
        with | _ -> None
        end
    | _ -> None
    end

| _ -> None

// let e_arrow2 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) =
//   let em (f : 'a -> 'b -> 'c) : t = Lam((fun (ta:t) -> match unembed ea ta with
//                                            | Some a -> embed eb (f a)
//                                            | None -> failwith "Cannot unembed argument"),
//                                     (fun _ -> type_of ea), None)
//   in
//   let un (lam : t) : option<('a -> 'b)> =
//       match lam with
//       | Lam (ft, _, _) -> Some (fun (x:'a) -> match unembed eb (ft (embed ea x)) with
//                                          | Some b -> b
//                                          | None -> failwith "Cannot unembed function result")
//       | _ -> None
//   in
//   mk_emb em un (make_arrow1 (type_of ea) (as_iarg (type_of eb)))
