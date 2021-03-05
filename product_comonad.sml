signature PRODUCT = sig
  type e
  type a
  type t = a * e

  val extract : t -> a

  structure Set : SET where type elem = t
  structure Lwd : LWD where type elem = t
end

functor Product (X : sig
  type e
  type a
  val compare : a * a -> order
end) : PRODUCT where type e = X.e where type a = X.a = struct
  type e = X.e
  type a = X.a
  type t = a * e

  fun extract (x, _) = x

  fun compare ((x, _), (y, _)) = X.compare (x, y)

  structure Set = Set (type t = t val compare = compare)
  structure Lwd = Lwd (Set)
end
