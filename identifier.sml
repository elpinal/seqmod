signature IDENT = sig
  type t

  val compare : t * t -> order
  val equal : t -> t -> bool

  val from_string : string -> t
  val show : t -> string

  structure Map : sig
    include MAP where type key = t

    exception MissingInLeft of key
    exception MissingInRight of key
    val app_eq : ('a * 'b -> unit) -> 'a t -> 'b t -> unit (* MissingInLeft, MissingInRight *)
  end
end

functor Ident () :> IDENT = struct
  type t = string

  val compare = String.compare
  fun equal x y = x = y

  fun from_string s = s
  fun show x = x

  structure Map = Map (type t = t val compare = compare)
  structure Map = struct
    open Map

    exception MissingInLeft of key
    exception MissingInRight of key

    fun app_eq f xs ys =
    let
      fun go (k, x, acc) =
        case lookup k acc of
             SOME y => delete k acc before f (x, y)
           | NONE   => raise MissingInRight k

      val ys' = fold go ys xs
    in
      (raise MissingInLeft (#1 (min ys')))
        handle Empty => ()
    end
  end
end

structure ModuleIdent = Ident ()
structure SignatureIdent = Ident ()
structure ValueIdent = Ident ()
structure TypeIdent = Ident ()

type module_ident = ModuleIdent.t
type signature_ident = SignatureIdent.t
type value_ident = ValueIdent.t
type type_ident = TypeIdent.t

type 'a location = module_ident list * 'a
