structure Internal = struct
  structure Kind = struct
    datatype t
      = KBase
      | KArrow of t * t

    exception Mismatch of t * t
    exception AppBase

    fun lift xs y = foldr (fn (x, acc) => KArrow(x, acc)) y xs

    fun unify k1 k2 =
      if k1 = k2
      then ()
      else raise Mismatch(k1, k2)

    fun args KBase            = []
      | args (KArrow(k1, k2)) = k1 :: args k2

    fun get_base f =
      fn KBase => ()
       | k     => raise f k

    val get_arrow =
      fn KArrow p => p
       | _        => raise AppBase

    local open Pretty in
      fun show_prec n =
        fn KBase        => "Type"
         | KArrow(x, y) => paren (2 < n) $ show_prec 3 x <+> "->" <+> show_prec 2 y

      fun show k = show_prec 0 k
    end
  end

  datatype kind = datatype Kind.t

  structure Quantified :> sig
    type 'a t
    type info

    datatype ident
      = T of type_ident
      | V of value_ident

    val from_body : 'a -> 'a t
    val quantify : info list -> 'a -> 'a t
    val quantify1 : kind -> ident -> 'a -> 'a t

    val map_with_location : (ident location -> ident location option) -> ('a -> 'b) -> 'a t -> 'b t
    val map :  ('a -> 'b) -> 'a t -> 'b t

    val apply : (kind list * 'a -> 'b) -> 'a t -> 'b
    val proj : 'a t -> info list * 'a
    val get_body : 'a t -> 'a

    val all_alive : 'a t -> bool

    structure Info : sig
      val extract : info -> kind
      val get_location : info -> ident location
      val map : (kind -> kind) -> info -> info
      val make_obsolete : (ident location -> bool) -> info -> info
    end
  end = struct
    datatype ident
      = T of type_ident
      | V of value_ident

    datatype status
      = Obsolete
      | Alive

    type info = kind * ident location * status

    type 'a t = info list * 'a

    fun from_body x = ([], x)

    fun quantify xs x = (xs, x)

    fun quantify1 k id x = ([(k, ([], id), Alive)], x)

    fun all_alive (xs, _) =
      List.all (fn (_, _, s) => s = Alive) xs

    fun map_with_location f g (xs, v) =
    let
      fun go (k, loc, Obsolete) = (k, loc, Obsolete)
        | go (k, loc, Alive)    =
            case f loc of
                 SOME loc' => (k, loc', Alive)
               | NONE      => (k, loc, Obsolete)
    in
      (List.map go xs, g v)
    end

    fun map f (xs, x) = (xs, f x)

    fun apply f ((xs, x) : 'a t) =
      f (List.map #1 xs : kind list, x)

    fun proj x = x

    fun get_body (_, x) = x

    structure Info = struct
      fun extract (k, _, _) = k
      fun get_location (_, loc, _) = loc
      fun map f (k, x, y) = (f k, x, y)

      fun make_obsolete _ (k, loc, Obsolete) = (k, loc, Obsolete)
        | make_obsolete f (k, loc, Alive)    =
            if f loc
            then (k, loc, Obsolete)
            else (k, loc, Alive)
    end
  end

  type 'a existential = 'a Quantified.t
  type 'a universal = 'a Quantified.t

  structure FVar :> sig
    type t

    val equal : t -> t -> bool
    val compare : t * t -> order
    val nth : t list * t -> int option
    val get_kind : t -> kind

    val fresh : kind -> t

    val show : t -> string

    structure Set : SET where type elem = t
    structure Map : MAP where type key = t
    structure Lwd : LWD where type elem = t
  end = struct
    type t = int * kind

    val counter = ref 0

    fun equal (x, _) (y, _) = x = y

    fun compare ((x, _), (y, _)) = Int.compare (x, y)

    fun fst (x, _) = x

    fun nth _ ([], _) = NONE
      | nth i (x :: xs, y) =
          if fst x = fst y
          then SOME i
          else nth (i + 1) (xs, y)

    val nth = fn p => nth 0 p

    fun get_kind (_, k) = k

    fun fresh k =
    let
      val n = !counter
    in
      counter := n + 1; (n, k)
    end

    fun show (n, _) = "!" ^ Int.toString n

    structure Set = Set (type t = t val compare = compare)
    structure Map = Map (type t = t val compare = compare)
    structure Lwd = Lwd (Set)
  end

  type fvar = FVar.t

  structure UVar :> sig
    type t

    val equal : t -> t -> bool
    val compare : t * t -> order

    val fresh : unit -> t

    val show : t -> string

    structure Set : SET where type elem = t
    structure Lwd : LWD where type elem = t
  end = struct
    type t = int

    val counter = ref 0

    fun equal x y = x = y

    val compare = Int.compare

    fun fresh () =
    let
      val n = !counter
    in
      counter := n + 1; n
    end

    fun show n = "?" ^ Int.toString n

    structure Set = Set (type t = t val compare = compare)
    structure Lwd = Lwd (Set)
  end

  type uvar = UVar.t

  structure Purity = struct
    datatype t
      = Impure
      | Pure

    fun show Impure = "impure"
      | show Pure   = "pure"
  end

  datatype purity = datatype Purity.t

  datatype tycon
    = Bound of int * int
    | Free of fvar
    | Unif of uvar * unif ref
    | Pack of asig
    | Abs of kind * tycon
    | App of tycon * tycon
    | Arrow of tycon * tycon
    | Unit
    | Prod of tycon * tycon
    | Sum of tycon * tycon

  and unif
    = Defined of tycon
    | Undefined

  and semsig
    = Struct of struct_
    | IArrow of (semsig * asig) universal
    | PArrow of (semsig * semsig) universal

  and asig
    = Exist of semsig existential

   (* We just let semantic paths be (unrestricted) type constructors
   * because we don't want to bother about normalization after substitution. *)
  and path
    = Path of tycon

  withtype scheme = int * tycon

  and struct_ =
    { m : semsig ModuleIdent.Map.t
    , s : asig SignatureIdent.Map.t
    , v : (path * (int * tycon)) ValueIdent.Map.t
    , t : (tycon * kind) TypeIdent.Map.t
    }

  structure U = Product (struct
    type a = uvar
    val compare = UVar.compare
    type e = unif ref
  end)

  exception Found of fvar
  exception Occur of uvar * tycon
  exception TypeMismatch of tycon * tycon
  exception PackageASigMismatch of asig * asig
  exception PackageSigMismatch of semsig * semsig
  exception SchemeMismatch of scheme * scheme

  exception NoSuchModuleComponent of module_ident
  exception NoSuchSignatureComponent of signature_ident
  exception NoSuchValueComponent of value_ident
  exception NoSuchTypeComponent of type_ident
  exception ProjFromFunctor of semsig
  exception MissingModuleInSubSignature of module_ident
  exception MissingSignatureInSubSignature of signature_ident
  exception MissingValueInSubSignature of value_ident
  exception MissingTypeInSubSignature of type_ident
  exception ImpureIsNotSubtypeOfPure of semsig * semsig
  exception NotSubtype of semsig * semsig
  exception CannotLookupType of semsig * semsig
  exception DuplicateModuleComponent of module_ident
  exception DuplicateSignatureComponent of signature_ident
  exception DuplicateValueComponent of value_ident
  exception DuplicateTypeComponent of type_ident
  exception NotProvenToBeExplicit of asig

  structure M : sig
    val show_tycon : tycon -> string
    val show_asig : asig -> string
    val show_semsig : semsig -> string
    val show_path : path -> string
    val show_scheme : scheme -> string

    val open_tycon : int -> tycon list -> tycon -> tycon
    val open_asig : int -> tycon list -> asig -> asig
    val open_semsig : int -> tycon list -> semsig -> semsig
    val open_struct : int -> tycon list -> struct_ -> struct_
    val open_path : int -> tycon list -> path -> path
    val open_scheme : int -> tycon list -> scheme -> scheme

    val close_tycon : int -> fvar list -> tycon -> tycon
    val close_asig : int -> fvar list -> asig -> asig
    val close_semsig : int -> fvar list -> semsig -> semsig
    val close_struct : int -> fvar list -> struct_ -> struct_
    val close_path : int -> fvar list -> path -> path
    val close_scheme : int -> fvar list -> scheme -> scheme

    val subst_semsig : (fvar * tycon) list -> semsig -> semsig

    val app_list : tycon -> tycon list -> tycon
    val abs_list : fvar list -> tycon -> tycon
    val from_path : path -> tycon
    val join : purity -> purity -> purity

    val empty_struct : struct_
    val insert_module : module_ident -> semsig -> struct_ -> struct_
    val insert_signature : signature_ident -> asig -> struct_ -> struct_
    val insert_value : value_ident -> path * scheme -> struct_ -> struct_
    val insert_type : type_ident -> tycon * kind -> struct_ -> struct_
    val disjoint_union : struct_ -> struct_ -> struct_
    val union : struct_ -> struct_ -> struct_ (* Right-biased. *)

    val reduce : tycon -> tycon

    val find_tycon : fvar list -> tycon -> unit (* Found *)
    val find_asig : fvar list -> asig -> unit (* Found *)
    val find_semsig : fvar list -> semsig -> unit (* Found *)
    val find_path : fvar list -> path -> unit (* Found *)
    val find_scheme : fvar list -> scheme -> unit (* Found *)

    (* Returns non-spurious unification variables in the canonical order. *)
    val uvs_tycon : tycon -> U.Lwd.t
    val uvs_asig : asig -> U.Lwd.t
    val uvs_semsig : semsig -> U.Lwd.t
    val uvs_path : path -> U.Lwd.t
    val uvs_scheme : scheme -> U.Lwd.t

    (* Returns non-spurious free variables in the canonical order. *)
    val fvs_tycon : FVar.Set.t -> tycon -> FVar.Lwd.t
    val fvs_semsig : FVar.Set.t -> semsig -> FVar.Lwd.t

    val unify : tycon -> tycon -> kind -> unit
    val str_unify : tycon -> tycon -> kind

    val get_structure : (semsig -> exn) -> semsig -> struct_
    val get_functor : (semsig -> exn) -> semsig -> (semsig * asig) universal * purity

    val proj_module : semsig -> module_ident -> semsig
    val proj_signature : semsig -> signature_ident -> asig
    val proj_value : semsig -> value_ident -> path * scheme
    val proj_type : semsig -> type_ident -> tycon * kind

    val proj_module_loc : semsig -> module_ident location -> semsig
    val proj_value_loc : semsig -> value_ident location -> path * scheme
    val proj_type_loc : semsig -> type_ident location -> tycon * kind

    val lookup_type : Quantified.ident location -> semsig -> semsig -> tycon
    val lookup_types : (Quantified.ident location * fvar) list -> semsig -> semsig -> tycon list

    val is_instance_of : scheme -> scheme -> unit
    val subtype_semsig : semsig -> semsig -> unit
    val subtype_asig : asig -> asig -> unit
    val match : semsig -> asig -> tycon list

    val instantiate : scheme -> tycon

    val norm_asig : asig -> asig

    val explicit_asig : asig -> unit
    val explicit_semsig : semsig -> unit

    val relative_location : module_ident location -> 'a location -> 'a location option
  end = struct
    fun open_tycon j tys =
      fn Bound(n, i) =>
           if n = j
           then List.nth (tys, i)
           else Bound(n, i)
       | Free fv => Free fv
       | Unif(v, r) =>
           let in
             case !r of
                  Defined ty => open_tycon j tys ty
                | Undefined  => Unif(v, r)
           end
       | Pack asig   => Pack (open_asig j tys asig)
       | Abs(k, x)   => Abs(k, open_tycon (j + 1) tys x)
       | App(x, y)   => App(open_tycon j tys x, open_tycon j tys y)
       | Arrow(x, y) => Arrow(open_tycon j tys x, open_tycon j tys y)
       | Unit        => Unit
       | Prod(x, y)  => Prod(open_tycon j tys x, open_tycon j tys y)
       | Sum(x, y)   => Sum(open_tycon j tys x, open_tycon j tys y)

    and open_asig j tys (Exist e) = Exist (Quantified.map (open_semsig (j + 1) tys) e)

    and open_semsig j tys =
      fn Struct s => Struct (open_struct j tys s)
       | IArrow u =>
           IArrow
             (Quantified.map
               (fn (x, y) => (open_semsig (j + 1) tys x, (open_asig (j + 1) tys y)))
               u
             )
       | PArrow u =>
           PArrow
             (Quantified.map
               (fn (x, y) => (open_semsig (j + 1) tys x, (open_semsig (j + 1) tys y)))
               u
             )

    and open_struct j tys {m, s, v, t} =
      { m = ModuleIdent.Map.map (open_semsig j tys) m
      , s = SignatureIdent.Map.map (open_asig j tys) s
      , v = ValueIdent.Map.map (fn (p, scheme) => (open_path j tys p, open_scheme j tys scheme)) v
      , t = TypeIdent.Map.map (fn (ty, k) => (open_tycon j tys ty, k)) t
      }

    and open_path j tys (Path ty) = Path (open_tycon j tys ty)

    and open_scheme j tys (n, ty) =
      (n, open_tycon (j + 1) tys ty)


    fun close_tycon j fvs =
      fn Bound(n, i) => Bound(n, i)
       | Free fv =>
           let in
             case FVar.nth (fvs, fv) of
                  SOME i => Bound(j, i)
                | NONE   => Free fv
           end
       | Unif(v, r) =>
           let in
             case !r of
                  Defined ty => close_tycon j fvs ty
                | Undefined  => Unif(v, r)
           end
       | Pack asig   => Pack (close_asig j fvs asig)
       | Abs(k, x)   => Abs(k, close_tycon (j + 1) fvs x)
       | App(x, y)   => App(close_tycon j fvs x, close_tycon j fvs y)
       | Arrow(x, y) => Arrow(close_tycon j fvs x, close_tycon j fvs y)
       | Unit        => Unit
       | Prod(x, y)  => Prod(close_tycon j fvs x, close_tycon j fvs y)
       | Sum(x, y)   => Sum(close_tycon j fvs x, close_tycon j fvs y)

    and close_asig j fvs (Exist e) = Exist (Quantified.map (close_semsig (j + 1) fvs) e)

    and close_semsig j fvs =
      fn Struct s => Struct (close_struct j fvs s)
       | IArrow u =>
           IArrow
             (Quantified.map
               (fn (x, y) => (close_semsig (j + 1) fvs x, (close_asig (j + 1) fvs y)))
               u
             )
       | PArrow u =>
           PArrow
             (Quantified.map
               (fn (x, y) => (close_semsig (j + 1) fvs x, (close_semsig (j + 1) fvs y)))
               u
             )

    and close_struct j fvs {m, s, v, t} =
      { m = ModuleIdent.Map.map (close_semsig j fvs) m
      , s = SignatureIdent.Map.map (close_asig j fvs) s
      , v = ValueIdent.Map.map (fn (p, scheme) => (close_path j fvs p, close_scheme j fvs scheme)) v
      , t = TypeIdent.Map.map (fn (ty, k) => (close_tycon j fvs ty, k)) t
      }

    and close_path j fvs (Path ty) = Path (close_tycon j fvs ty)

    and close_scheme j fvs (n, ty) =
      (n, close_tycon (j + 1) fvs ty)

    fun subst_semsig (xs : (fvar * tycon) list) x =
      open_semsig 0 (map #2 xs)
      (close_semsig 0 (map #1 xs) x)

    fun app_list x []        = x
      | app_list x (y :: ys) = app_list (App(x, y)) ys

    fun abs_list fvs x =
      foldr (fn (fv, acc) => Abs(FVar.get_kind fv, close_tycon 0 [fv] acc)) x fvs

    fun from_path (Path ty) = ty

    fun join Pure Pure = Pure
      | join _ _       = Impure

    val empty_struct =
      { m = ModuleIdent.Map.empty
      , s = SignatureIdent.Map.empty
      , v = ValueIdent.Map.empty
      , t = TypeIdent.Map.empty
      }

    fun insert_module id x {m, s, v, t} =
      { m = ModuleIdent.Map.insert id x m
      , s = s
      , v = v
      , t = t
      }

    fun insert_signature id x {m, s, v, t} =
      { m = m
      , s = SignatureIdent.Map.insert id x s
      , v = v
      , t = t
      }

    fun insert_value id x {m, s, v, t} =
      { m = m
      , s = s
      , v = ValueIdent.Map.insert id x v
      , t = t
      }

    fun insert_type id x {m, s, v, t} =
      { m = m
      , s = s
      , v = v
      , t = TypeIdent.Map.insert id x t
      }

    fun disjoint_union (x : struct_) (y : struct_) =
    let
      fun fm (k, v, acc) =
        if ModuleIdent.Map.member k (#m y)
        then raise DuplicateModuleComponent k
        else ModuleIdent.Map.insert k v acc

      fun fs (k, v, acc) =
        if SignatureIdent.Map.member k (#s y)
        then raise DuplicateSignatureComponent k
        else SignatureIdent.Map.insert k v acc

      fun fv (k, v, acc) =
        if ValueIdent.Map.member k (#v y)
        then raise DuplicateValueComponent k
        else ValueIdent.Map.insert k v acc

      fun ft (k, v, acc) =
        if TypeIdent.Map.member k (#t y)
        then raise DuplicateTypeComponent k
        else TypeIdent.Map.insert k v acc
    in
      { m = ModuleIdent.Map.fold fm (#m y) (#m x)
      , s = SignatureIdent.Map.fold fs (#s y) (#s x)
      , v = ValueIdent.Map.fold fv (#v y) (#v x)
      , t = TypeIdent.Map.fold ft (#t y) (#t x)
      }
    end

    fun union (x : struct_) (y : struct_) =
    let
      fun fm (k, v, acc) =
        if ModuleIdent.Map.member k (#m y)
        then acc
        else ModuleIdent.Map.insert k v acc

      fun fs (k, v, acc) =
        if SignatureIdent.Map.member k (#s y)
        then acc
        else SignatureIdent.Map.insert k v acc

      fun fv (k, v, acc) =
        if ValueIdent.Map.member k (#v y)
        then acc
        else ValueIdent.Map.insert k v acc

      fun ft (k, v, acc) =
        if TypeIdent.Map.member k (#t y)
        then acc
        else TypeIdent.Map.insert k v acc
    in
      { m = ModuleIdent.Map.fold fm (#m y) (#m x)
      , s = SignatureIdent.Map.fold fs (#s y) (#s x)
      , v = ValueIdent.Map.fold fv (#v y) (#v x)
      , t = TypeIdent.Map.fold ft (#t y) (#t x)
      }
    end

    fun reduce (App(x, y))  = reduce' (reduce x) y
      | reduce (Unif(v, r)) =
          let in
            case !r of
                 Defined ty => reduce ty
               | Undefined  => Unif(v, r)
          end
      | reduce ty = ty

    and reduce' (Abs(_, x)) y = reduce (open_tycon 0 [y] x)
      | reduce' x y           = App(x, y)

    fun find_tycon' fvs =
      fn Bound _ => ()
       | Free fv =>
           let in
             case FVar.nth (fvs, fv) of
                  SOME _ => raise Found fv
                | NONE   => ()
           end
       | Unif _      => () (* Assume the argument has been `reduce`d. *)
       | Pack asig   => find_asig fvs asig
       | Abs(k, x)   => find_tycon fvs (open_tycon 0 [Free (FVar.fresh k)] x)
       | App(x, y)   => find_tycon' fvs x before find_tycon fvs y
       | Arrow(x, y) => find_tycon fvs x before find_tycon fvs y
       | Unit        => ()
       | Prod(x, y)  => find_tycon fvs x before find_tycon fvs y
       | Sum(x, y)   => find_tycon fvs x before find_tycon fvs y

    and find_tycon fvs ty = find_tycon' fvs (reduce ty)

    and find_asig fvs (Exist e) =
    let
      val s = Quantified.apply (fn (ks, s) => open_semsig 0 (map (Free o FVar.fresh) ks) s) e
    in
      find_semsig fvs s
    end

    and find_semsig fvs =
      fn Struct {m, s, v, t} =>
           ( ModuleIdent.Map.app (find_semsig fvs) m
           ; SignatureIdent.Map.app (find_asig fvs) s
           ; ValueIdent.Map.app (fn (p, s) => find_path fvs p before find_scheme fvs s) v
           ; TypeIdent.Map.app (fn (ty, _) => find_tycon fvs ty) t
           )
       | IArrow u =>
           let
             fun f (ks, (s, asig)) =
             let val xs = map (Free o FVar.fresh) ks in
               ( open_semsig 0 xs s
               , open_asig 0 xs asig
               )
             end
             val (s, asig) = Quantified.apply f u
           in
             find_semsig fvs s; find_asig fvs asig
           end
       | PArrow u =>
           let
             fun f (ks, (s, s')) =
             let val xs = map (Free o FVar.fresh) ks in
               ( open_semsig 0 xs s
               , open_semsig 0 xs s'
               )
             end
             val (s, s') = Quantified.apply f u
           in
             find_semsig fvs s; find_semsig fvs s'
           end

    and find_path fvs (Path ty) = find_tycon fvs ty

    and find_scheme fvs (n, ty) =
      find_tycon fvs (open_tycon 0 (List.tabulate (n, fn _ => Free (FVar.fresh KBase))) ty)

    fun uvs_tycon' ty : U.Lwd.t =
    let val op@ = U.Lwd.append in
      case ty of
           Bound _     => U.Lwd.empty
         | Free _      => U.Lwd.empty
         | Unif(v, r)  => U.Lwd.singleton (v, r)
         | Pack asig   => uvs_asig asig
         | Abs(k, x)   => uvs_tycon (open_tycon 0 [Free (FVar.fresh k)] x)
         | App(x, y)   => uvs_tycon' x @ uvs_tycon y
         | Arrow(x, y) => uvs_tycon x @ uvs_tycon y
         | Unit        => U.Lwd.empty
         | Prod(x, y)  => uvs_tycon x @ uvs_tycon y
         | Sum(x, y)   => uvs_tycon x @ uvs_tycon y
    end

    and uvs_tycon ty = uvs_tycon' (reduce ty)

    and uvs_asig (Exist e) =
    let
      val s = Quantified.apply (fn (ks, s) => open_semsig 0 (map (Free o FVar.fresh) ks) s) e
    in
      uvs_semsig s
    end

    and uvs_semsig s =
    let val op@ = U.Lwd.append in
      case s of
           Struct {m, s, v, t} =>
             ModuleIdent.Map.fold (fn (_, s, acc) => acc @ uvs_semsig s) U.Lwd.empty m
             @ SignatureIdent.Map.fold (fn (_, asig, acc) => acc @ uvs_asig asig) U.Lwd.empty s
             @ ValueIdent.Map.fold (fn (_, (p, scheme), acc) => acc @ uvs_path p @ uvs_scheme scheme) U.Lwd.empty v
             @ TypeIdent.Map.fold (fn (_, (ty, _), acc) => acc @ uvs_tycon ty) U.Lwd.empty t
         | IArrow u =>
             let
               fun f (ks, (s, asig)) =
               let val fvs = map (Free o FVar.fresh) ks in
                 U.Lwd.append
                   ( uvs_semsig (open_semsig 0 fvs s)
                   , uvs_asig (open_asig 0 fvs asig)
                   )
               end
             in
               Quantified.apply f u
             end
         | PArrow u =>
             let
               fun f (ks, (s, s')) =
               let val fvs = map (Free o FVar.fresh) ks in
                 U.Lwd.append
                   ( uvs_semsig (open_semsig 0 fvs s)
                   , uvs_semsig (open_semsig 0 fvs s')
                   )
               end
             in
               Quantified.apply f u
             end
    end

    and uvs_path (Path ty) = uvs_tycon ty

    and uvs_scheme (n, ty) =
      uvs_tycon (open_tycon 0 (List.tabulate (n, fn _ => Free (FVar.fresh KBase))) ty)


    fun fvs_tycon' pred ty : FVar.Lwd.t =
    let val op@ = FVar.Lwd.append in
      case ty of
           Bound _     => FVar.Lwd.empty
         | Free fv     => if FVar.Set.member fv pred then FVar.Lwd.singleton fv else FVar.Lwd.empty
         | Unif _      => FVar.Lwd.empty
         | Pack asig   => fvs_asig pred asig
         | Abs(k, x)   => fvs_tycon pred (open_tycon 0 [Free (FVar.fresh k)] x)
         | App(x, y)   => fvs_tycon' pred x @ fvs_tycon pred y
         | Arrow(x, y) => fvs_tycon pred x @ fvs_tycon pred y
         | Unit        => FVar.Lwd.empty
         | Prod(x, y)  => fvs_tycon pred x @ fvs_tycon pred y
         | Sum(x, y)   => fvs_tycon pred x @ fvs_tycon pred y
    end

    and fvs_tycon pred ty = fvs_tycon' pred (reduce ty)

    and fvs_asig pred (Exist e) =
    let
      val s = Quantified.apply (fn (ks, s) => open_semsig 0 (map (Free o FVar.fresh) ks) s) e
    in
      fvs_semsig pred s
    end

    and fvs_semsig pred s =
    let val op@ = FVar.Lwd.append in
      case s of
           Struct {m, s, v, t} =>
             ModuleIdent.Map.fold (fn (_, s, acc) => acc @ fvs_semsig pred s) FVar.Lwd.empty m
             @ SignatureIdent.Map.fold (fn (_, asig, acc) => acc @ fvs_asig pred asig) FVar.Lwd.empty s
             @ ValueIdent.Map.fold (fn (_, (p, scheme), acc) => acc @ fvs_path pred p @ fvs_scheme pred scheme) FVar.Lwd.empty v
             @ TypeIdent.Map.fold (fn (_, (ty, _), acc) => acc @ fvs_tycon pred ty) FVar.Lwd.empty t
         | IArrow u =>
             let
               fun f (ks, (s, asig)) =
               let val fvs = map (Free o FVar.fresh) ks in
                 FVar.Lwd.append
                   ( fvs_semsig pred (open_semsig 0 fvs s)
                   , fvs_asig pred (open_asig 0 fvs asig)
                   )
               end
             in
               Quantified.apply f u
             end
         | PArrow u =>
             let
               fun f (ks, (s, s')) =
               let val fvs = map (Free o FVar.fresh) ks in
                 FVar.Lwd.append
                   ( fvs_semsig pred (open_semsig 0 fvs s)
                   , fvs_semsig pred (open_semsig 0 fvs s')
                   )
               end
             in
               Quantified.apply f u
             end
    end

    and fvs_path pred (Path ty) = fvs_tycon pred ty

    and fvs_scheme pred (n, ty) =
      fvs_tycon pred (open_tycon 0 (List.tabulate (n, fn _ => Free (FVar.fresh KBase))) ty)

    fun unify_uvar ((v, r) : U.t) (y : tycon) : unit =
      case y of
           Unif(v', _) =>
             if UVar.equal v v'
             then ()
             else r := Defined y
         | _ =>
             if U.Lwd.member (v, r) (uvs_tycon y)
             then raise Occur(v, y)
             else r := Defined y

    fun unify ty1 ty2 k =
      case k of
           KBase          => ignore (str_unify (reduce ty1) (reduce ty2))
         | KArrow(k1, k2) =>
             let val fv = Free (FVar.fresh k1) in
               unify (App(ty1, fv)) (App(ty2, fv)) k2
             end

    and str_unify ty1 ty2 =
      case (ty1, ty2) of
           (Free v1, Free v2) =>
             if FVar.equal v1 v2
             then FVar.get_kind v1
             else raise TypeMismatch(ty1, ty2)
         | (Unif x, _) => KBase before unify_uvar x ty2
         | (_, Unif x) => KBase before unify_uvar x ty1
         | (Pack asig1, Pack asig2) => KBase before unify_asig asig1 asig2
         | (App(x1, x2), App(y1, y2)) =>
             let in
               case str_unify x1 y1 of
                    KBase => raise Kind.AppBase
                  | KArrow(k1, k2) => k2 before unify x2 y2 k1
             end
         | (Arrow(x1, x2), Arrow(y1, y2)) =>
             KBase
             before unify x1 y1 KBase
             before unify x2 y2 KBase
         | (Unit, Unit) => KBase
         | (Prod(x1, x2), Prod(y1, y2)) =>
             KBase
             before unify x1 y1 KBase
             before unify x2 y2 KBase
         | (Sum(x1, x2), Sum(y1, y2)) =>
             KBase
             before unify x1 y1 KBase
             before unify x2 y2 KBase
         | _ => raise TypeMismatch(ty1, ty2)

    and unify_asig (Exist asig1) (Exist asig2) : unit =
      let
        val (xs, s1) = Quantified.proj asig1
        val (ys, s2) = Quantified.proj asig2

        fun f (i1, i2) =
        let
          val k1 = Quantified.Info.extract i1
          val k2 = Quantified.Info.extract i2
        in
          if k1 = k2
          then Free (FVar.fresh k1)
          else raise PackageASigMismatch(Exist asig1, Exist asig2)
        end

        val fvs = ListPair.mapEq f (xs, ys)
          handle ListPair.UnequalLengths => raise PackageASigMismatch(Exist asig1, Exist asig2)
      in
        unify_semsig (open_semsig 0 fvs s1) (open_semsig 0 fvs s2)
      end

    and unify_semsig s1 s2 : unit =
      case (s1, s2) of
           (Struct x, Struct y) =>
             ( ModuleIdent.Map.app_eq (fn (x, y) => unify_semsig x y) (#m x) (#m y)
             ; SignatureIdent.Map.app_eq (fn (x, y) => unify_asig x y) (#s x) (#s y)
             ; ValueIdent.Map.app_eq (fn ((p1, s1), (p2, s2)) => unify_path p1 p2 before unify_scheme s1 s2) (#v x) (#v y)
             ; TypeIdent.Map.app_eq (fn ((ty1, k1), (ty2, k2)) => Kind.unify k1 k2 before unify ty1 ty2 k1) (#t x) (#t y)
             )
         | (IArrow u1, IArrow u2) =>
             let
               val (xs, (s1, asig1)) = Quantified.proj u1
               val (ys, (s2, asig2)) = Quantified.proj u2

               fun f (i1, i2) =
               let
                 val k1 = Quantified.Info.extract i1
                 val k2 = Quantified.Info.extract i2
               in
                 if k1 = k2
                 then Free (FVar.fresh k1)
                 else raise PackageSigMismatch(IArrow u1, IArrow u2)
               end

               val fvs = ListPair.mapEq f (xs, ys)
                 handle ListPair.UnequalLengths => raise PackageSigMismatch(IArrow u1, IArrow u2)
             in
               unify_semsig (open_semsig 0 fvs s1) (open_semsig 0 fvs s2);
               unify_asig (open_asig 0 fvs asig1) (open_asig 0 fvs asig2)
             end
         | (PArrow u1, PArrow u2) =>
             let
               val (xs, (s1, s1')) = Quantified.proj u1
               val (ys, (s2, s2')) = Quantified.proj u2

               fun f (i1, i2) =
               let
                 val k1 = Quantified.Info.extract i1
                 val k2 = Quantified.Info.extract i2
               in
                 if k1 = k2
                 then Free (FVar.fresh k1)
                 else raise PackageSigMismatch(PArrow u1, PArrow u2)
               end

               val fvs = ListPair.mapEq f (xs, ys)
                 handle ListPair.UnequalLengths => raise PackageSigMismatch(PArrow u1, PArrow u2)
             in
               unify_semsig (open_semsig 0 fvs s1) (open_semsig 0 fvs s2);
               unify_semsig (open_semsig 0 fvs s1') (open_semsig 0 fvs s2')
             end
         | _ => raise PackageSigMismatch(s1, s2)

    and unify_path p1 p2 =
      unify (from_path p1) (from_path p2) KBase

    and unify_scheme (s1 as (n1, x)) (s2 as (n2, y)) =
      if n1 <> n2
      then raise SchemeMismatch(s1, s2)
      else
        let
          val fvs = List.tabulate (n1, fn _ => Free (FVar.fresh KBase))
          val x = open_tycon 0 fvs x
          val y = open_tycon 0 fvs y
        in
          unify x y KBase
        end

    val quantify_codomain : (semsig * semsig) universal -> (semsig * asig) universal =
      Quantified.map (fn (x, y) => (x, Exist (Quantified.from_body y)))

    fun get_structure f =
      fn Struct s => s
       | s        => raise f s

    fun get_functor f =
      fn IArrow u => (u, Impure)
       | PArrow u => (quantify_codomain u, Pure)
       | s        => raise f s

    fun proj_module s id =
      valOf (ModuleIdent.Map.lookup id (#m (get_structure ProjFromFunctor s)))
        handle Option => raise NoSuchModuleComponent id

    fun proj_signature s id =
      valOf (SignatureIdent.Map.lookup id (#s (get_structure ProjFromFunctor s)))
        handle Option => raise NoSuchSignatureComponent id

    fun proj_value s id =
      valOf (ValueIdent.Map.lookup id (#v (get_structure ProjFromFunctor s)))
        handle Option => raise NoSuchValueComponent id

    fun proj_type s id =
      valOf (TypeIdent.Map.lookup id (#t (get_structure ProjFromFunctor s)))
        handle Option => raise NoSuchTypeComponent id

    fun proj_module_loc s (mids, mid) =
    let val s' = foldl (fn (mid, acc) => proj_module acc mid) s mids in
      proj_module s' mid
    end

    fun proj_value_loc s (mids, vid) =
    let val s' = foldl (fn (mid, acc) => proj_module acc mid) s mids in
      proj_value s' vid
    end

    fun proj_type_loc s (mids, tid) =
    let val s' = foldl (fn (mid, acc) => proj_module acc mid) s mids in
      proj_type s' tid
    end

    fun lookup_type loc s1 s2 =
      case (s1, s2) of
           (Struct x, Struct y) =>
             let in
               case loc of
                    (mid :: mids, id) =>
                      let in
                        lookup_type
                          (mids, id)
                          (valOf (ModuleIdent.Map.lookup mid (#m x)))
                          (valOf (ModuleIdent.Map.lookup mid (#m y)))
                          handle Option => raise CannotLookupType(s1, s2)
                      end
                  | ([], Quantified.V vid) =>
                      let
                        val (p1, _) = valOf (ValueIdent.Map.lookup vid (#v x))
                          handle Option => raise CannotLookupType(s1, s2)
                      in
                        from_path p1
                      end
                  | ([], Quantified.T tid) =>
                      let
                        val (ty1, k1) = valOf (TypeIdent.Map.lookup tid (#t x))
                          handle Option => raise CannotLookupType(s1, s2)
                        val (_, k2) = valOf (TypeIdent.Map.lookup tid (#t y))
                      in
                        Kind.unify k1 k2; ty1
                      end
             end
         | (PArrow u1, PArrow u2) =>
             let
               val (xs, (s1, s1')) = Quantified.proj u1
               val (ys, (s2, s2')) = Quantified.proj u2

               val fvs1 = map (FVar.fresh o Quantified.Info.extract) xs
               val s1 = open_semsig 0 (map Free fvs1) s1
               val s1' = open_semsig 0 (map Free fvs1) s1'

               val fvs2 = map (FVar.fresh o Quantified.Info.extract) ys
               val s2 = open_semsig 0 (map Free fvs2) s2
               val s2' = open_semsig 0 (map Free fvs2) s2'

               val tys = lookup_types (ListPair.zipEq (map Quantified.Info.get_location xs, fvs1)) s2 s1

               val ty = lookup_type loc (subst_semsig (ListPair.zipEq (fvs1, tys)) s1') s2'
             in
               abs_list fvs2 ty
             end
         | _ => raise CannotLookupType(s1, s2)

    and lookup_types xs s1 s2 : tycon list =
    let
      fun f ((loc, fv), (tys, s2')) =
      let
        val ty = lookup_type loc s1 s2'
      in
        (tys @ [ty], subst_semsig [(fv, ty)] s2)
      end
    in
      #1 (foldl f ([], s2) xs)
    end

    fun subtype_type_component (ty1, k1) (ty2, k2) =
      ( Kind.unify k1 k2
      ; unify ty1 ty2 k1
      )

    fun is_instance_of (n1, ty1) (n2, ty2) =
    let
      val x = open_tycon 0 (List.tabulate (n1, fn _ => Free (FVar.fresh KBase))) ty1
      val y = open_tycon 0 (List.tabulate (n2, fn _ => Unif(UVar.fresh (), ref Undefined))) ty2
    in
      unify x y KBase
    end

    fun subtype_value_component (p1, s1) (p2, s2) =
      ( is_instance_of s2 s1
      ; unify_path p1 p2
      )

    fun subtype_semsig s1 s2 =
      case (s1, s2) of
           (Struct x, Struct y) =>
             let
               fun fm (id, s2, ()) =
                 subtype_semsig (valOf (ModuleIdent.Map.lookup id (#m x))) s2
                   handle Option => raise MissingModuleInSubSignature id

               fun fs (id, asig2, ()) =
                 subtype_asig (valOf (SignatureIdent.Map.lookup id (#s x))) asig2
                   handle Option => raise MissingSignatureInSubSignature id

               fun fv (id, s2, ()) =
                 subtype_value_component (valOf (ValueIdent.Map.lookup id (#v x))) s2
                   handle Option => raise MissingValueInSubSignature id

               fun ft (id, e2, ()) =
                 subtype_type_component (valOf (TypeIdent.Map.lookup id (#t x))) e2
                   handle Option => raise MissingTypeInSubSignature id
             in
               ModuleIdent.Map.fold fm () (#m y);
               SignatureIdent.Map.fold fs () (#s y);
               ValueIdent.Map.fold fv () (#v y);
               TypeIdent.Map.fold ft () (#t y)
             end
         | (PArrow u1, PArrow u2) => subtype_functor (quantify_codomain u1) (quantify_codomain u2)
         | (IArrow u1, IArrow u2) => subtype_functor u1 u2
         | (PArrow u1, IArrow u2) => subtype_functor (quantify_codomain u1) u2
         | (IArrow _, PArrow _) => raise ImpureIsNotSubtypeOfPure(s1, s2)
         | _                    => raise NotSubtype(s1, s2)

    and subtype_functor u1 u2 =
    let
      val (xs, (s1, asig1)) = Quantified.proj u1
      val (ys, (s2, asig2)) = Quantified.proj u2

      val fvs2 = map (Free o FVar.fresh o Quantified.Info.extract) ys
      val s2 = open_semsig 0 fvs2 s2
      val asig2 = open_asig 0 fvs2 asig2

      val tys = match s2 (Exist (Quantified.quantify xs s1))
    in
      subtype_asig (open_asig 0 tys asig1) asig2
    end

    and subtype_asig (Exist asig1) asig2 =
    let
      val (xs, s1) = Quantified.proj asig1
      val fvs = map (Free o FVar.fresh o Quantified.Info.extract) xs
      val s1 = open_semsig 0 fvs s1
    in
      ignore (match s1 asig2)
    end

    and match s1 (Exist asig2) =
    let
      val (xs, s2) = Quantified.proj asig2
      val fvs = map (FVar.fresh o Quantified.Info.extract) xs
      val s2 = open_semsig 0 (map Free fvs) s2

      val tys = lookup_types (ListPair.zipEq (map Quantified.Info.get_location xs, fvs)) s1 s2
      val s2 = open_semsig 0 tys (Quantified.get_body asig2)
      val () = subtype_semsig s1 s2
    in
      tys
    end

    fun instantiate (n, ty) =
    let
      val x = open_tycon 0 (List.tabulate (n, fn _ => Unif(UVar.fresh (), ref Undefined))) ty
    in
      x
    end

    fun norm_asig (Exist asig) =
    let
      val (xs, s) = Quantified.proj asig
      val fvs = map (FVar.fresh o Quantified.Info.extract) xs
      val s = open_semsig 0 (map Free fvs) s
      val s = norm_semsig s

      val set = FVar.Set.from_list fvs
      val m = FVar.Map.from_list (ListPair.zipEq (fvs, xs))
      val fvs' = FVar.Lwd.to_list (fvs_semsig set s)
      val xs' = map (fn fv => valOf (FVar.Map.lookup fv m)) fvs'
    in
      Exist (Quantified.quantify xs' (close_semsig 0 fvs' s))
    end

    and norm_semsig s =
      case s of
           Struct {m,s,v,t} => Struct
             { m = ModuleIdent.Map.map norm_semsig m
             , s = SignatureIdent.Map.map norm_asig s
             , v = v
             , t = t
             }
         | IArrow u =>
             let
               val (xs, (s, asig)) = Quantified.proj u
               val fvs = map (FVar.fresh o Quantified.Info.extract) xs
               val s = open_semsig 0 (map Free fvs) s
               val s = norm_semsig s
               val asig = open_asig 0 (map Free fvs) asig
               val asig = norm_asig asig

               val set = FVar.Set.from_list fvs
               val m = FVar.Map.from_list (ListPair.zipEq (fvs, xs))
               val fvs' = FVar.Lwd.to_list (fvs_semsig set s)
               val xs' = map (fn fv => valOf (FVar.Map.lookup fv m)) fvs'
             in
               IArrow (Quantified.quantify xs' (close_semsig 0 fvs' s, close_asig 0 fvs' asig))
             end
         | PArrow u =>
             let
               val (xs, (s, s2)) = Quantified.proj u
               val fvs = map (FVar.fresh o Quantified.Info.extract) xs
               val s = open_semsig 0 (map Free fvs) s
               val s = norm_semsig s
               val s2 = open_semsig 0 (map Free fvs) s2
               val s2 = norm_semsig s2

               val set = FVar.Set.from_list fvs
               val m = FVar.Map.from_list (ListPair.zipEq (fvs, xs))
               val fvs' = FVar.Lwd.to_list (fvs_semsig set s)
               val xs' = map (fn fv => valOf (FVar.Map.lookup fv m)) fvs'
             in
               PArrow (Quantified.quantify xs' (close_semsig 0 fvs' s, close_semsig 0 fvs' s2))
             end

    local open Pretty in
      fun show_tycon_prec n =
        fn Bound _ => raise Fail "unreachable"
         | Free fv => FVar.show fv
         | Unif(uv, r) =>
             let in
               case !r of
                    Defined ty => show_tycon_prec n ty
                  | Undefined  => UVar.show uv
             end
         | Pack asig => paren (4 < n) $ "pack" <+> show_asig_prec 5 asig
         | Abs(k, x) =>
             let val fv = FVar.fresh k in
               "λ" <> FVar.show fv <> ":" <> Kind.show k <> "." <+>
                 show_tycon_prec 0 (open_tycon 0 [Free fv] x)
             end
         | App(x, y) => paren (4 < n) $ show_tycon_prec 4 x <+> show_tycon_prec 5 y
         | Arrow(x, y) => paren (2 < n) $ show_tycon_prec 3 x <+> "->" <+> show_tycon_prec 2 y
         | Unit => "unit"
         | Prod(x, y) => paren (3 < n) $ show_tycon_prec 4 x <+> "&" <+> show_tycon_prec 4 y
         | Sum(x, y) => paren (3 < n) $ show_tycon_prec 4 x <+> "+" <+> show_tycon_prec 4 y

      and show_asig_prec n (Exist asig) =
        let
          val (xs, s) = Quantified.proj asig
          val fvs = map (FVar.fresh o Quantified.Info.extract) xs
          val s = open_semsig 0 (map Free fvs) s
        in
          if null xs
          then show_semsig_prec n s
          else paren (2 < n) $ "∃" <> list FVar.show fvs <> "." <> show_semsig_prec 0 s
        end

      and show_semsig_prec n =
        fn Struct {m,s,v,t} =>
             let
               val l1 = map #2 $ ModuleIdent.Map.to_asc_list $
                 ModuleIdent.Map.map_with_key
                   (fn (id, x) => ModuleIdent.show id <> ":" <> show_semsig_prec 0 x) m
               val l2 = map #2 $ SignatureIdent.Map.to_asc_list $
                 SignatureIdent.Map.map_with_key
                   (fn (id, x) => SignatureIdent.show id <> "=" <> show_asig_prec 0 x) s
               val l3 = map #2 $ ValueIdent.Map.to_asc_list $
                 ValueIdent.Map.map_with_key
                   (fn (id, (p, s)) => ValueIdent.show id <> paren true ("=" <> show_path_prec 0 p) <> ":" <> show_scheme_prec 0 s) v
               val l4 = map #2 $ TypeIdent.Map.to_asc_list $
                 TypeIdent.Map.map_with_key
                   (fn (id, (ty, k)) => TypeIdent.show id <> paren true ("=" <> show_tycon_prec 0 ty) <> ":" <> Kind.show k) t
             in
               brace $ list (fn x => x) (l1 @ l2 @ l3 @ l4)
             end
         | IArrow u =>
             let
               val (xs, (s1, asig2)) = Quantified.proj u
               val fvs = map (FVar.fresh o Quantified.Info.extract) xs
               val s1 = open_semsig 0 (map Free fvs) s1
               val asig2 = open_asig 0 (map Free fvs) asig2

               val head =
                 if null xs
                 then ""
                 else "∀" <> list FVar.show fvs <> "."
             in
               paren (2 < n) $ head <> show_semsig_prec 3 s1 <+> "->I" <+> show_asig_prec 2 asig2
             end
         | PArrow u =>
             let
               val (xs, (s1, s2)) = Quantified.proj u
               val fvs = map (FVar.fresh o Quantified.Info.extract) xs
               val s1 = open_semsig 0 (map Free fvs) s1
               val s2 = open_semsig 0 (map Free fvs) s2

               val head =
                 if null xs
                 then ""
                 else "∀" <> list FVar.show fvs <> "."
             in
               paren (2 < n) $ head <> show_semsig_prec 3 s1 <+> "->P" <+> show_semsig_prec 2 s2
             end

      and show_path_prec n (Path ty) = show_tycon_prec n ty

      and show_scheme_prec n (m, ty) =
        let
          val fvs = List.tabulate (m, fn _ => FVar.fresh KBase)
          val ty = open_tycon 0 (map Free fvs) ty
        in
          if null fvs
          then show_tycon_prec n ty
          else paren (2 < n) $ "∀" <> list FVar.show fvs <> "." <> show_tycon_prec 0 ty
        end

      val show_tycon = show_tycon_prec 0
      val show_asig = show_asig_prec 0
      val show_semsig = show_semsig_prec 0
      val show_path = show_path_prec 0
      val show_scheme = show_scheme_prec 0
    end

    (* Even for non-locally-closed signatures. *)
    val rec explicit_semsig =
      fn Struct{m,s,...} =>
           ( ModuleIdent.Map.app explicit_semsig m
           ; SignatureIdent.Map.app explicit_asig s
           )
       | IArrow u =>
           let val (xs, (s, asig)) = Quantified.proj u in
             explicit_asig (Exist (Quantified.quantify xs s));
             explicit_asig asig
           end
       | PArrow u =>
           let val (xs, (s, s')) = Quantified.proj u in
             explicit_asig (Exist (Quantified.quantify xs s));
             explicit_semsig s'
           end

    and explicit_asig = fn Exist asig =>
      if Quantified.all_alive asig (* This is conservative approximation. *)
      then explicit_semsig (Quantified.get_body asig)
      else raise NotProvenToBeExplicit (Exist asig)

    fun relative_location (mids, mid) (mids', id) =
      case (mids, mids') of
           (_, []) => NONE
         | ([], x :: xs) =>
             if ModuleIdent.equal x mid
             then SOME (xs, id)
             else NONE
         | (x :: xs, y :: ys) =>
             if ModuleIdent.equal x y
             then relative_location (xs, mid) (ys, id)
             else NONE
  end
  open M
end
