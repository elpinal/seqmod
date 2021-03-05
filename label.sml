structure Label :> sig
  type t

  val compare : t * t -> order
end = struct
  type t = string
  val compare = String.compare
end

type label = Label.t

structure Record = Map (Label)
