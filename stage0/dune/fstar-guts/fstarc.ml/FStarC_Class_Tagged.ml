open Prims
type 'a tagged = {
  tag_of: 'a -> Prims.string }
let __proj__Mktagged__item__tag_of (projectee : 'a tagged) :
  'a -> Prims.string= match projectee with | { tag_of;_} -> tag_of
let tag_of (projectee : 'a tagged) : 'a -> Prims.string=
  __proj__Mktagged__item__tag_of projectee
