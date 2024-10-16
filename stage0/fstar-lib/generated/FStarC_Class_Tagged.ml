open Prims
type 'a tagged = {
  tag_of: 'a -> Prims.string }
let __proj__Mktagged__item__tag_of : 'a . 'a tagged -> 'a -> Prims.string =
  fun projectee -> match projectee with | { tag_of;_} -> tag_of
let tag_of : 'a . 'a tagged -> 'a -> Prims.string =
  fun projectee -> match projectee with | { tag_of = tag_of1;_} -> tag_of1