{
  val x = ()

  signature S = {
    module M : {type t}
  } where module M = {type t = unit val y = x}
}
