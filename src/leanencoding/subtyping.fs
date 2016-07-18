module FStar.LeanEncoding.Subtyping
open FStar.Syntax.Syntax

module TcEnv = FStar.TypeChecker.Env
module SS = FStar.Syntax.Subst
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module N = FStar.TypeChecker.Normalize

//a cast between [t1] and [t2], 
//where t1 and t2 are F* types 
//and [t1] and [t2] are their corresponding lean translations.
type cast = 
    | Dummy                //TODO: remove this
    | NoCast               //[t1] is definitionally equal to [t2] in Lean
    | EqCast               //[t1] is provably equal to [t2] Lean
    | DropRefinement       //[t1] is castable to [t2], via elt_of
    | AddRefinement        //[t1] is castable to [t2], via tag
    | RepackRefinement     //[t1] is castable to [t2], via a tag . elt_of <-- this should be the only occurrence of transitivity?
    | Arrow of cast * cast //[t1] is definitionally equal to a s1 -> s1', in Lean
			   //[t2] is definitionally equal to a s2 -> s2', in Lean
			   //given Arrow c c', s2  is castable to s1  via c
  			   //                  s1' is castable to s2' via c'
let cast t1 t2 = Dummy

let rec univ_eq u1 u2 = 
  match u1, u2 with
  | U_zero, U_zero -> true
  | U_name x, U_name y -> x = y
  | U_succ u, U_succ v -> univ_eq u v
  | U_max us1, U_max us2 -> List.length us1 = List.length us2 && List.forall2 univ_eq us1 us2
  | _ -> false

let const_eq c1 c2 = false

(*
   nat <: nat

   x:int{x>=1} <: x:int{x>=0}


*)

(*  -- t1 and t2 are expected to already be well-typed terms, of type Type_i
    -- They are expected to be in strong normal form
    -- They are expected to not have any Tm_uvar's
    -- Their variables are all typed intrinsically, meaning that we do not rely on env for their types
    -- env may be redundant, TBD
    We return None if t1 is not a subtype of t2
    And Some c, where c is a lean term for casting a term of lean type [t1] to [t2]
*)
let rec subtype (env:TcEnv.env) (t1:typ) (t2:typ) : option<cast> =
    let t1, t2 = U.unmeta t1, U.unmeta t2 in
    match t1.n, t2.n with
    | Tm_delayed _, _
    | _, Tm_delayed _
    | Tm_bvar _, _
    | _, Tm_bvar _
    | Tm_uvar _, _
    | _, Tm_uvar _ 
    | Tm_meta _, _
    | _, Tm_meta _ 
    | Tm_unknown, _
    | _, Tm_unknown 
    | Tm_abs _, _
    | _, Tm_abs _ 
    | Tm_let _, _
    | _, Tm_let _ -> failwith "Impossible"

    | Tm_constant c1, Tm_constant c2 -> 
      if const_eq c1 c2
      then Some NoCast
      else Some EqCast

    | Tm_name x, Tm_name y -> 
      //These can only be related by ~, the equivalence on types
      if S.bv_eq x y
      then Some NoCast
      else Some EqCast

    | Tm_type u1, Tm_type u2 -> 
      if univ_eq u1 u2
      then Some NoCast
      else None

    | Tm_fvar fv1, Tm_fvar fv2 -> 
      if S.fv_eq fv1 fv2
      then Some NoCast
      else None

    | Tm_uinst(t1, us1), Tm_uinst(t2, us2) -> 
      if (List.length us1 = List.length us2
          && List.forall2 univ_eq us1 us2)
      then subtype env t1 t2
      else None

    | Tm_refine _, _ 
    | _, Tm_refine _ -> 
      let t1 = N.normalize_refinement [N.Beta; N.UnfoldUntil Delta_constant] env t1 in
      let t2 = N.normalize_refinement [N.Beta; N.UnfoldUntil Delta_constant] env t2 in
      begin match (SS.compress t1).n, (SS.compress t2).n with
            | Tm_refine(x, phi1), Tm_refine(y, phi2) ->
              begin match subtype env x.sort y.sort with 
                | Some NoCast
                | Some EqCast
                | _ -> failwith "NYI"
              end
            | _ -> failwith "NYI"
     end

    | _ -> None
    
//  | Tm_arrow      of binders * comp                              (* (xi:ti) -> M t' wp *)
//  | Tm_refine     of bv * term                                   (* x:t{phi} *)
//  | Tm_app        of term * args                                 (* h tau_1 ... tau_n, args in order from left to right *)
//  | Tm_match      of term * list<branch>                         (* match e with b1 ... bn *)
//  | Tm_ascribed   of term * either<term,comp> * option<lident>   (* an effect label is the third arg, filled in by the type-checker *)
