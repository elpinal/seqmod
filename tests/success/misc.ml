{
  signature S = {type t}
  type p = pack S
  module X = {
    val x = pack {type t = unit} : S
  }
  module Y = unpack X.x : S

  module F = fn X : {} => {}

  module M = {
    val id = fn x => x
  }

  module A = M :> {val id 'a : 'a -> 'a}
  module B = M :> {val id : unit -> unit}
}
