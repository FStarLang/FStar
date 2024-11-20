open Prims
type 'a showable = {
  show: 'a -> Prims.string }
let __proj__Mkshowable__item__show : 'a . 'a showable -> 'a -> Prims.string =
  fun projectee -> match projectee with | { show;_} -> show
let show : 'a . 'a showable -> 'a -> Prims.string =
  fun projectee -> match projectee with | { show = show1;_} -> show1
let (showable_unit : unit showable) = { show = (fun uu___ -> "()") }
let (showable_bool : Prims.bool showable) = { show = Prims.string_of_bool }
let (showable_nat : Prims.nat showable) = { show = Prims.string_of_int }
let (showable_int : Prims.int showable) = { show = Prims.string_of_int }
let (showable_string : Prims.string showable) =
  { show = (fun x -> Prims.strcat "\"" (Prims.strcat x "\"")) }
let show_list : 'a . 'a showable -> 'a Prims.list showable =
  fun uu___ -> { show = ((FStarC_Common.string_of_list ()) (show uu___)) }
let show_option :
  'a . 'a showable -> 'a FStar_Pervasives_Native.option showable =
  fun uu___ -> { show = (FStarC_Common.string_of_option (show uu___)) }
let show_either :
  'a 'b .
    'a showable -> 'b showable -> ('a, 'b) FStar_Pervasives.either showable
  =
  fun uu___ ->
    fun uu___1 ->
      {
        show =
          (fun uu___2 ->
             match uu___2 with
             | FStar_Pervasives.Inl x ->
                 let uu___3 = show uu___ x in Prims.strcat "Inl " uu___3
             | FStar_Pervasives.Inr y ->
                 let uu___3 = show uu___1 y in Prims.strcat "Inr " uu___3)
      }
let show_tuple2 : 'a 'b . 'a showable -> 'b showable -> ('a * 'b) showable =
  fun uu___ ->
    fun uu___1 ->
      {
        show =
          (fun uu___2 ->
             match uu___2 with
             | (x1, x2) ->
                 let uu___3 =
                   let uu___4 = show uu___ x1 in
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = show uu___1 x2 in Prims.strcat uu___7 ")" in
                     Prims.strcat ", " uu___6 in
                   Prims.strcat uu___4 uu___5 in
                 Prims.strcat "(" uu___3)
      }
let show_tuple3 :
  'a 'b 'c .
    'a showable -> 'b showable -> 'c showable -> ('a * 'b * 'c) showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        {
          show =
            (fun uu___3 ->
               match uu___3 with
               | (x1, x2, x3) ->
                   let uu___4 =
                     let uu___5 = show uu___ x1 in
                     let uu___6 =
                       let uu___7 =
                         let uu___8 = show uu___1 x2 in
                         let uu___9 =
                           let uu___10 =
                             let uu___11 = show uu___2 x3 in
                             Prims.strcat uu___11 ")" in
                           Prims.strcat ", " uu___10 in
                         Prims.strcat uu___8 uu___9 in
                       Prims.strcat ", " uu___7 in
                     Prims.strcat uu___5 uu___6 in
                   Prims.strcat "(" uu___4)
        }
let show_tuple4 :
  'a 'b 'c 'd .
    'a showable ->
      'b showable ->
        'c showable -> 'd showable -> ('a * 'b * 'c * 'd) showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          {
            show =
              (fun uu___4 ->
                 match uu___4 with
                 | (x1, x2, x3, x4) ->
                     let uu___5 =
                       let uu___6 = show uu___ x1 in
                       let uu___7 =
                         let uu___8 =
                           let uu___9 = show uu___1 x2 in
                           let uu___10 =
                             let uu___11 =
                               let uu___12 = show uu___2 x3 in
                               let uu___13 =
                                 let uu___14 =
                                   let uu___15 = show uu___3 x4 in
                                   Prims.strcat uu___15 ")" in
                                 Prims.strcat ", " uu___14 in
                               Prims.strcat uu___12 uu___13 in
                             Prims.strcat ", " uu___11 in
                           Prims.strcat uu___9 uu___10 in
                         Prims.strcat ", " uu___8 in
                       Prims.strcat uu___6 uu___7 in
                     Prims.strcat "(" uu___5)
          }
let show_tuple5 :
  'a 'b 'c 'd 'e .
    'a showable ->
      'b showable ->
        'c showable ->
          'd showable -> 'e showable -> ('a * 'b * 'c * 'd * 'e) showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            {
              show =
                (fun uu___5 ->
                   match uu___5 with
                   | (x1, x2, x3, x4, x5) ->
                       let uu___6 =
                         let uu___7 = show uu___ x1 in
                         let uu___8 =
                           let uu___9 =
                             let uu___10 = show uu___1 x2 in
                             let uu___11 =
                               let uu___12 =
                                 let uu___13 = show uu___2 x3 in
                                 let uu___14 =
                                   let uu___15 =
                                     let uu___16 = show uu___3 x4 in
                                     let uu___17 =
                                       let uu___18 =
                                         let uu___19 = show uu___4 x5 in
                                         Prims.strcat uu___19 ")" in
                                       Prims.strcat ", " uu___18 in
                                     Prims.strcat uu___16 uu___17 in
                                   Prims.strcat ", " uu___15 in
                                 Prims.strcat uu___13 uu___14 in
                               Prims.strcat ", " uu___12 in
                             Prims.strcat uu___10 uu___11 in
                           Prims.strcat ", " uu___9 in
                         Prims.strcat uu___7 uu___8 in
                       Prims.strcat "(" uu___6)
            }
let show_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a showable ->
      'b showable ->
        'c showable ->
          'd showable ->
            'e showable ->
              'f showable -> ('a * 'b * 'c * 'd * 'e * 'f) showable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              {
                show =
                  (fun uu___6 ->
                     match uu___6 with
                     | (x1, x2, x3, x4, x5, x6) ->
                         let uu___7 =
                           let uu___8 = show uu___ x1 in
                           let uu___9 =
                             let uu___10 =
                               let uu___11 = show uu___1 x2 in
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 = show uu___2 x3 in
                                   let uu___15 =
                                     let uu___16 =
                                       let uu___17 = show uu___3 x4 in
                                       let uu___18 =
                                         let uu___19 =
                                           let uu___20 = show uu___4 x5 in
                                           let uu___21 =
                                             let uu___22 =
                                               let uu___23 = show uu___5 x6 in
                                               Prims.strcat uu___23 ")" in
                                             Prims.strcat ", " uu___22 in
                                           Prims.strcat uu___20 uu___21 in
                                         Prims.strcat ", " uu___19 in
                                       Prims.strcat uu___17 uu___18 in
                                     Prims.strcat ", " uu___16 in
                                   Prims.strcat uu___14 uu___15 in
                                 Prims.strcat ", " uu___13 in
                               Prims.strcat uu___11 uu___12 in
                             Prims.strcat ", " uu___10 in
                           Prims.strcat uu___8 uu___9 in
                         Prims.strcat "(" uu___7)
              }