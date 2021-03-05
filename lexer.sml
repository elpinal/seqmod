structure LexerError = struct
  exception IllegalChar of position * char
  exception QuoteIdent of position * char option
end

structure Lexer : sig
  val lex : string -> Token.t Stream.stream
end = struct
  structure R = Reader (Position)

  open LexerError

  val left_paren_stack = ref []
  val left_brace_stack = ref []

  fun ident r =
  let
    fun go cs =
      let val c = R.peek r handle R.EOF => #" " in
        if Char.isAlphaNum c orelse c = #"_"
        then go (c :: cs before R.proceed r c)
        else String.implode (rev cs)
      end
  in
    go [R.next r]
  end

  fun quote r =
    case R.peek_option r of
         SOME c =>
           if Char.isAlpha c
           then Token.QUOTE_IDENT (ident r)
           else raise QuoteIdent(R.pos r, SOME c)
       | NONE => raise QuoteIdent(R.pos r, NONE)

  fun upper r = Token.UPPER_IDENT (ident r)

  fun lower r =
    case ident r of
         "pack"      => Token.PACK
       | "unpack"    => Token.UNPACK
       | "fn"        => Token.FN
       | "case"      => Token.CASE
       | "inl"       => Token.INL
       | "inr"       => Token.INR
       | "fst"       => Token.FST
       | "snd"       => Token.SND
       | "module"    => Token.MODULE
       | "signature" => Token.SIGNATURE
       | "val"       => Token.VAL
       | "type"      => Token.TYPE
       | "include"   => Token.INCLUDE
       | "where"     => Token.WHERE
       | "like"      => Token.LIKE
       | s           => Token.LOWER_IDENT s

  fun hyphen r =
    case R.peek_option r of
         SOME #">" => (R.proceed r #">"; Token.RARROW)
       | _         => Token.MINUS

  fun equal r =
    case R.peek_option r of
         SOME #">" => (R.proceed r #">"; Token.RDARROW)
       | _         => Token.EQUAL

  fun colon r =
    case R.peek_option r of
         SOME #">" => (R.proceed r #">"; Token.COLON_GT)
       | _         => Token.COLON

  fun comment r =
    case R.peek_option r of
         SOME #"\n" => R.proceed r #"\n"
       | SOME c     => (R.proceed r c; comment r)
       | NONE       => ()

  val rec lex1 : R.t -> Token.t = fn r =>
  let
    val c = R.peek r
  in
    case c of
         #" "  => (R.proceed r c; lex1 r)
       | #"\n" => (R.proceed r c; lex1 r)
       | #"\t" => (R.proceed r c; lex1 r)
       | #"\r" => (R.proceed r c; lex1 r)

       | #";" => (R.proceed r c; comment r; lex1 r)

       | #"(" =>
           let val l = ref Token.Normal in
             R.proceed r c;
             left_paren_stack := l :: !left_paren_stack;
             Token.LPAREN l
           end

       | #")" =>
           let
             val l =
               case !left_paren_stack of
                    l :: ls => l before left_paren_stack := ls
                  | []      => raise Fail "unreachable"
           in
             R.proceed r c;
             case R.peek_option r of
                  SOME #"." => (l := Token.DotInRight; Token.RPAREN)
                | _         => Token.RPAREN
           end

       | #"{" =>
           let val l = ref Token.Normal in
             R.proceed r c;
             left_brace_stack := l :: !left_brace_stack;
             Token.LBRACE l
           end

       | #"}" =>
           let
             val l =
               case !left_brace_stack of
                    l :: ls => l before left_brace_stack := ls
                  | []      => raise Fail "unreachable"
           in
             R.proceed r c;
             case R.peek_option r of
                  SOME #"." => (l := Token.DotInRight; Token.RBRACE)
                | _         => Token.RBRACE
           end


       | #"-" => (R.proceed r c; hyphen r)
       | #"=" => (R.proceed r c; equal r)
       | #"&" => (R.proceed r c; Token.AMPERSAND)
       | #"+" => (R.proceed r c; Token.PLUS)
       | #":" => (R.proceed r c; colon r)
       | #"," => (R.proceed r c; Token.COMMA)
       | #"." => (R.proceed r c; Token.DOT)
       | #"|" => (R.proceed r c; Token.BAR)

       | #"'" => (R.proceed r c; quote r)

       | _ =>
           if Char.isUpper c
           then upper r
           else if Char.isLower c
           then lower r
           else raise IllegalChar(R.pos r, c)
  end

  fun lex s =
  let
    val r = R.new s

    fun go acc = go (lex1 r :: acc)
      handle R.EOF => acc

    fun f (Token.LPAREN l) =
          let in
            case !l of
                 Token.DotInRight => Token.LPAREN_PROJ
               | _                => Token.LPAREN l
          end
      | f (Token.LBRACE l) =
          let in
            case !l of
                 Token.DotInRight => Token.LBRACE_PROJ
               | _                => Token.LBRACE l
          end
      | f t = t
  in
    Stream.fromList (rev (map f (go [])))
  end
end
