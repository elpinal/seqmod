(* List without duplicates. *)
signature LWD = sig
  type t
  type elem

  val empty : t
  val singleton : elem -> t
  val append : t * t -> t

  val delete : elem -> t -> t

  val member : elem -> t -> bool

  val to_list : t -> elem list
  val foldl : (elem * 'a -> 'a) -> 'a -> t -> 'a
  val foldr : (elem * 'a -> 'a) -> 'a -> t -> 'a
end

functor Lwd (Set : sig
  type t
  type elem

  val empty : t
  val singleton : elem -> t
  val insert : elem -> t -> t
  val member : elem -> t -> bool
  val delete : elem -> t -> t
end) :> LWD where type elem = Set.elem = struct
  type elem = Set.elem
  type t = elem list * Set.t

  val empty = ([], Set.empty)
  fun singleton x = ([x], Set.singleton x)

  fun append ((l1, s1), (l2, _)) =
  let
    fun f (x, acc) =
      if Set.member x s1
      then acc
      else (#1 acc @ [x], Set.insert x (#2 acc))
  in
    foldl f (l1, s1) l2
  end

  fun delete' _ [] = []
    | delete' x (y :: ys) =
        if Set.member x (Set.singleton y)
        then ys
        else y :: delete' x ys

  fun delete x (l, s) =
    if Set.member x s
    then (delete' x l, Set.delete x s)
    else (l, s)

  fun member x (_, s) = Set.member x s

  fun to_list (l, _) = l

  fun foldl f x (l, _) = List.foldl f x l
  fun foldr f x (l, _) = List.foldr f x l
end
