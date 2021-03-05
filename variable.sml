structure TVar :> sig
  type t

  val compare : t * t -> order

  val from_string : string -> t
  val show : t -> string

  structure Lwd : LWD where type elem = t
end = struct
  type t = string

  val compare = String.compare

  fun from_string s = s
  fun show s = "'" ^ s

  structure Set = Set (type t = t val compare = compare)
  structure Lwd = Lwd (Set)
end

type tvar = TVar.t
