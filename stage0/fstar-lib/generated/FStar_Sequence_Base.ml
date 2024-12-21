open Prims
type 'ty seq = 'ty Prims.list
let length : 'ty . 'ty seq -> Prims.nat =
  fun uu___ -> (Obj.magic FStar_List_Tot_Base.length) uu___
let empty : 'ty . unit -> 'ty seq =
  fun uu___ -> (fun uu___ -> Obj.magic []) uu___
let singleton : 'ty . 'ty -> 'ty seq =
  fun uu___ -> (fun v -> Obj.magic [v]) uu___
let index : 'ty . 'ty seq -> Prims.nat -> 'ty =
  fun s -> fun i -> FStar_List_Tot_Base.index (Obj.magic s) i
let op_Dollar_At : 'uuuuu . unit -> 'uuuuu seq -> Prims.nat -> 'uuuuu =
  fun uu___ -> index
let build : 'ty . 'ty seq -> 'ty -> 'ty seq =
  fun uu___1 ->
    fun uu___ ->
      (fun s ->
         fun v -> Obj.magic (FStar_List_Tot_Base.append (Obj.magic s) [v]))
        uu___1 uu___
let op_Dollar_Colon_Colon :
  'uuuuu . unit -> 'uuuuu seq -> 'uuuuu -> 'uuuuu seq = fun uu___ -> build
let append : 'ty . 'ty seq -> 'ty seq -> 'ty seq =
  fun uu___1 ->
    fun uu___ -> (Obj.magic FStar_List_Tot_Base.append) uu___1 uu___
let op_Dollar_Plus : 'uuuuu . unit -> 'uuuuu seq -> 'uuuuu seq -> 'uuuuu seq
  = fun uu___ -> append
let update : 'ty . 'ty seq -> Prims.nat -> 'ty -> 'ty seq =
  fun s ->
    fun i ->
      fun v ->
        let uu___ = FStar_List_Tot_Base.split3 (Obj.magic s) i in
        match uu___ with
        | (s1, uu___1, s2) ->
            append (Obj.magic s1) (append (Obj.magic [v]) (Obj.magic s2))
type ('ty, 's, 'v) contains = Obj.t
let take : 'ty . 'ty seq -> Prims.nat -> 'ty seq =
  fun uu___1 ->
    fun uu___ ->
      (fun s ->
         fun howMany ->
           let uu___ = FStar_List_Tot_Base.splitAt howMany (Obj.magic s) in
           match uu___ with | (result, uu___1) -> Obj.magic result) uu___1
        uu___
let drop : 'ty . 'ty seq -> Prims.nat -> 'ty seq =
  fun uu___1 ->
    fun uu___ ->
      (fun s ->
         fun howMany ->
           let uu___ = FStar_List_Tot_Base.splitAt howMany (Obj.magic s) in
           match uu___ with | (uu___1, result) -> Obj.magic result) uu___1
        uu___
type ('ty, 's0, 's1) equal = unit
type ('uuuuu, 's0, 's1) op_Dollar_Equals_Equals = unit
type ('ty, 's0, 's1) is_prefix = unit
type ('uuuuu, 's0, 's1) op_Dollar_Less_Equals = unit
let rank : 'ty . 'ty -> 'ty = fun v -> v
type length_of_empty_is_zero_fact = unit
type length_zero_implies_empty_fact = unit
type singleton_length_one_fact = unit
type build_increments_length_fact = unit
type 'uuuuu index_into_build_fact = unit
type append_sums_lengths_fact = unit
type 'uuuuu index_into_singleton_fact = unit
type 'uuuuu index_after_append_fact = unit
type update_maintains_length_fact = unit
type update_then_index_fact = unit
type contains_iff_exists_index_fact = unit
type empty_doesnt_contain_anything_fact = unit
type build_contains_equiv_fact = unit
type take_contains_equiv_exists_fact = unit
type drop_contains_equiv_exists_fact = unit
type equal_def_fact = unit
type extensionality_fact = unit
type is_prefix_def_fact = unit
type take_length_fact = unit
type 'uuuuu index_into_take_fact = unit
type drop_length_fact = unit
type 'uuuuu index_into_drop_fact = unit
type 'uuuuu drop_index_offset_fact = unit
type 'uuuuu append_then_take_or_drop_fact = unit
type 'uuuuu take_commutes_with_in_range_update_fact = unit
type 'uuuuu take_ignores_out_of_range_update_fact = unit
type 'uuuuu drop_commutes_with_in_range_update_fact = unit
type 'uuuuu drop_ignores_out_of_range_update_fact = unit
type 'uuuuu drop_commutes_with_build_fact = unit
type rank_def_fact = unit
type element_ranks_less_fact = unit
type drop_ranks_less_fact = unit
type take_ranks_less_fact = unit
type append_take_drop_ranks_less_fact = unit
type drop_zero_fact = unit
type take_zero_fact = unit
type 'uuuuu drop_then_drop_fact = unit
type all_seq_facts = unit