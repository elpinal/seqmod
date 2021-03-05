structure Position :> sig
  include POSITION

  val show : position -> string
end = struct
  type position = int * int

  val initial = (1, 1)

  fun next c (x, y) =
    case c of
         #"\n" => (x + 1, 1)
       | _     => (x, y + 1)

  fun show (x, y) = Int.toString x ^ "." ^ Int.toString y
end

type position = Position.position
