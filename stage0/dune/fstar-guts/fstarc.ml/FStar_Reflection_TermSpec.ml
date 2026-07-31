open Prims
let rec map_dec :
  'a 'b 'tb . 'tb -> ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun top f l ->
    match l with | [] -> [] | x::xs -> (f x) :: (map_dec top f xs)
let opt_dec (top : 'tb) (f : 'a -> 'b)
  (o : 'a FStar_Pervasives_Native.option) :
  'b FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some (f x)
let denote_universes (us : FStarC_Reflection_Types.universe Prims.list) :
  unit Prims.list= FStar_List_Tot_Base.map (fun uu___ -> ()) us
let rec denote_terms (ts : FStarC_Reflection_Types.term Prims.list) :
  unit Prims.list=
  match ts with | [] -> [] | t::ts1 -> () :: (denote_terms ts1)
and denote_args (a : FStarC_Reflection_V2_Data.argv Prims.list) :
  (unit * unit) Prims.list=
  match a with | [] -> [] | (t, q)::a1 -> ((), ()) :: (denote_args a1)
and denote_opt_term
  (o : FStarC_Reflection_Types.term FStar_Pervasives_Native.option) :
  unit FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some ()
and denote_ret
  (o :
    FStarC_Syntax_Syntax.match_returns_ascription
      FStar_Pervasives_Native.option)
  :
  (unit * ((unit, unit) FStar_Pervasives.either * unit
    FStar_Pervasives_Native.option * Prims.bool))
    FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (b, (FStar_Pervasives.Inl t, tacopt, eq)) ->
      FStar_Pervasives_Native.Some
        ((), ((FStar_Pervasives.Inl ()), (denote_opt_term tacopt), eq))
  | FStar_Pervasives_Native.Some (b, (FStar_Pervasives.Inr c, tacopt, eq)) ->
      FStar_Pervasives_Native.Some
        ((), ((FStar_Pervasives.Inr ()), (denote_opt_term tacopt), eq))
and denote_branches (brs : FStarC_Reflection_V2_Data.branch Prims.list) :
  (unit * unit) Prims.list=
  match brs with
  | [] -> []
  | (p, t)::brs1 -> ((), ()) :: (denote_branches brs1)
and denote_subpats
  (ps : (FStarC_Reflection_V2_Data.pattern * Prims.bool) Prims.list) :
  (unit * Prims.bool) Prims.list=
  match ps with | [] -> [] | (p, b)::ps1 -> ((), b) :: (denote_subpats ps1)
type subst_spec_elt =
  | DTs of Prims.nat * unit 
  | NTs of Prims.nat * unit 
  | NDs of Prims.nat * Prims.nat 
let uu___is_DTs (projectee : subst_spec_elt) : Prims.bool=
  match projectee with | DTs (_0, _1) -> true | uu___ -> false
let __proj__DTs__item___0 (projectee : subst_spec_elt) : Prims.nat=
  match projectee with | DTs (_0, _1) -> _0
let uu___is_NTs (projectee : subst_spec_elt) : Prims.bool=
  match projectee with | NTs (_0, _1) -> true | uu___ -> false
let __proj__NTs__item___0 (projectee : subst_spec_elt) : Prims.nat=
  match projectee with | NTs (_0, _1) -> _0
let uu___is_NDs (projectee : subst_spec_elt) : Prims.bool=
  match projectee with | NDs (_0, _1) -> true | uu___ -> false
let __proj__NDs__item___0 (projectee : subst_spec_elt) : Prims.nat=
  match projectee with | NDs (_0, _1) -> _0
let __proj__NDs__item___1 (projectee : subst_spec_elt) : Prims.nat=
  match projectee with | NDs (_0, _1) -> _1
let shift_subst_spec_elt (n : Prims.nat) (uu___ : subst_spec_elt) :
  subst_spec_elt=
  match uu___ with
  | DTs (i, t) -> DTs ((i + n), ())
  | NTs (x, t) -> NTs (x, ())
  | NDs (x, i) -> NDs (x, (i + n))
type subst_spec = subst_spec_elt Prims.list
let shift_subst_spec_n (n : Prims.nat) :
  subst_spec_elt Prims.list -> subst_spec_elt Prims.list=
  FStar_List_Tot_Base.map (shift_subst_spec_elt n)
let shift_subst_spec :
  subst_spec_elt Prims.list -> subst_spec_elt Prims.list=
  shift_subst_spec_n Prims.int_one
let rec find_matching_subst_spec_elt_bv (s : subst_spec) (i : Prims.nat) :
  subst_spec_elt FStar_Pervasives_Native.option=
  match s with
  | [] -> FStar_Pervasives_Native.None
  | (DTs (j, t))::ss ->
      if j = i
      then FStar_Pervasives_Native.Some (DTs (j, ()))
      else find_matching_subst_spec_elt_bv ss i
  | uu___::ss -> find_matching_subst_spec_elt_bv ss i
let rec find_matching_subst_spec_elt_var (s : subst_spec) (uniq : Prims.nat)
  : subst_spec_elt FStar_Pervasives_Native.option=
  match s with
  | [] -> FStar_Pervasives_Native.None
  | (NTs (y, uu___))::rest ->
      if y = uniq
      then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.hd s)
      else find_matching_subst_spec_elt_var rest uniq
  | (NDs (y, uu___))::rest ->
      if y = uniq
      then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.hd s)
      else find_matching_subst_spec_elt_var rest uniq
  | uu___::rest -> find_matching_subst_spec_elt_var rest uniq
