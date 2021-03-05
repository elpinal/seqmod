open SeqMod

fun main () =
let
  val arg =
    case CommandLine.arguments () of
         x :: _ => x
       | []     => fail "missing arguments"

  val m = parse_file arg
  val (asig, purity) = elaborate m
in
  print ("purity: " ^ Internal.Purity.show purity ^ "\n");
  print (Internal.show_asig asig ^ "\n")
end

val () = main ()
