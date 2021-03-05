infix 4 <+>
infixr 0 $

structure Pretty :> sig
  type t = string

  val $ : ('a -> 'b) * 'a -> 'b

  val <> : t * t -> t
  val <+> : t * t -> t

  val paren : bool -> t -> t
  val brace : t -> t
  val bracket : t -> t

  (* Without parentheses *)
  val list : ('a -> t) -> 'a list -> t
end = struct
  type t = string

  fun f $ x = f x

  fun x <> y = x ^ y
  fun x <+> y = x <> " " <> y

  fun paren true s  = "(" <> s <> ")"
    | paren false s = s

  fun brace s = "{" <> s <> "}"

  fun bracket s = "[" <> s <> "]"

  fun non_empty f x []        = f x
    | non_empty f x [y]       = f x <> "," <+> f y
    | non_empty f x (y :: zs) = f x <> "," <+> non_empty f y zs

  fun list _ []        = ""
    | list f (x :: xs) = non_empty f x xs
end
