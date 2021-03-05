{
  module M = {
    type t = unit
    val x = ()
  }

  signature S = like M

  signature T = {
    module N : {type t}
    module O = N
  }
}
