structure Token = struct
  datatype left
    = Normal
    | DotInRight

  datatype t
    = LOWER_IDENT of string
    | UPPER_IDENT of string
    | QUOTE_IDENT of string

    | LPAREN of left ref
    | RPAREN
    | LBRACE of left ref
    | RBRACE

    | LPAREN_PROJ
    | LBRACE_PROJ

    | RARROW
    | RDARROW
    | AMPERSAND
    | PLUS
    | MINUS
    | COLON
    | COLON_GT
    | COMMA
    | DOT
    | EQUAL
    | BAR

    | PACK
    | UNPACK
    | FN
    | CASE
    | INL
    | INR
    | FST
    | SND
    | MODULE
    | SIGNATURE
    | VAL
    | TYPE
    | INCLUDE
    | WHERE
    | LIKE

  val show =
    fn LOWER_IDENT s => s
     | UPPER_IDENT s => s
     | QUOTE_IDENT s => "'" ^ s

     | LPAREN _ => "("
     | RPAREN   => ")"
     | LBRACE _ => "{"
     | RBRACE   => "}"

     | LPAREN_PROJ => "("
     | LBRACE_PROJ => "{"

     | RARROW    => "->"
     | RDARROW   => "=>"
     | AMPERSAND => "&"
     | PLUS      => "+"
     | MINUS     => "-"
     | COLON     => ":"
     | COLON_GT  => ":>"
     | COMMA     => ","
     | DOT       => "."
     | EQUAL     => "="
     | BAR       => "|"

     | PACK      => "pack"
     | UNPACK    => "unpack"
     | FN        => "fn"
     | CASE      => "case"
     | INL       => "inl"
     | INR       => "inr"
     | FST       => "fst"
     | SND       => "snd"
     | MODULE    => "module"
     | SIGNATURE => "signature"
     | VAL       => "val"
     | TYPE      => "type"
     | INCLUDE   => "include"
     | WHERE     => "where"
     | LIKE      => "like"
end
