module FStar.Pervasives

type either<'a,'b> =
  | Inl of 'a
  | Inr of 'b
