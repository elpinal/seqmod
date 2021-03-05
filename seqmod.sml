structure SeqMod : sig
  val fail : string -> 'a
  val parse_string : string -> Syntax.module
  val parse_file : string -> Syntax.module
  val elaborate : Syntax.module -> Internal.asig * Internal.purity
end = struct
  fun fail s =
    ( TextIO.output (TextIO.stdErr, s ^ "\n")
    ; OS.Process.exit OS.Process.failure
    )

  open Pretty

  fun parse_string s =
  let
    val s = Lexer.lex s
    val t = #1 (Parser.parse s)
  in
    t
  end handle
      LexerError.IllegalChar(p, c) =>
        fail (Position.show p ^ ": illegal character: " ^ Char.toString c)
    | ParserError.UnexpectedEOF => fail "unexpected end of file"
    | ParserError.UnexpectedToken t => fail ("unexpected token: " ^ Token.show t)

  fun parse_file name =
  let
    val ins = TextIO.openIn name handle IO.Io _ => fail ("cannot open: " ^ name)
    val s = TextIO.inputAll ins
    val () = TextIO.closeIn ins
  in
    parse_string s
  end

  fun elaborate m = Elaboration.elaborate_module Env.initial m
    handle
        Internal.TypeMismatch(x, y) =>
          fail ("type mismatch:" <+> Internal.show_tycon x <+> "vs" <+> Internal.show_tycon y)
      | Env.Module.Unbound id => fail ("unbaund module identifier:" <+> ModuleIdent.show id)
      | Env.Signature.Unbound id => fail ("unbaund signature identifier:" <+> SignatureIdent.show id)
      | Env.Value.Unbound id => fail ("unbaund value identifier:" <+> ValueIdent.show id)
      | Env.Type.Unbound id => fail ("unbaund type identifier:" <+> TypeIdent.show id)
      | Env.TVar.Unbound id => fail ("unbaund type variable:" <+> TVar.show id)
      | Internal.CannotLookupType(x, y) =>
          fail ("type lookup error:" <+> Internal.show_semsig x <+> "vs" <+> Internal.show_semsig y)
end
