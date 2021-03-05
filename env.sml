local
  open Internal
in
  structure Env :> sig
    type t

    val initial : t
    val insert : struct_ -> t -> t

    val uvs : t -> U.Set.t

    structure Module : sig
      exception Unbound of module_ident

      val lookup : t -> module_ident -> semsig
      val insert : module_ident -> semsig -> t -> t
    end

    structure Signature : sig
      exception Unbound of signature_ident

      val lookup : t -> signature_ident -> asig
    end

    structure Value : sig
      exception Unbound of value_ident

      datatype entry
        = ModL of path * scheme
        | CoreL of tycon

      val lookup : t -> value_ident -> entry
      val insert : value_ident -> entry -> t -> t
    end

    structure Type : sig
      exception Unbound of type_ident

      val lookup : t -> type_ident -> tycon * kind
    end

    structure TVar : sig
      exception Unbound of tvar

      val lookup : t -> tvar -> fvar
      val insert : tvar -> fvar -> t -> t
    end
  end = struct
    datatype value_entry
      = ModL of path * scheme
      | CoreL of tycon

    structure T = Map (TVar)

    type t =
      { m : semsig ModuleIdent.Map.t
      , s : asig SignatureIdent.Map.t
      , v : value_entry ValueIdent.Map.t
      , t : (tycon * kind) TypeIdent.Map.t
      , tv : fvar T.t
      }

    val initial : t =
      { m = ModuleIdent.Map.empty
      , s = SignatureIdent.Map.empty
      , v = ValueIdent.Map.empty
      , t = TypeIdent.Map.from_list [(TypeIdent.from_string "unit", (Unit, KBase))]
      , tv = T.empty
      }

    fun insert (s : struct_) (e : t) =
      ( { m = ModuleIdent.Map.fold (fn (k, v, acc) => ModuleIdent.Map.insert k v acc) (#m e) (#m s)
        , s = SignatureIdent.Map.fold (fn (k, v, acc) => SignatureIdent.Map.insert k v acc) (#s e) (#s s)
        , v = ValueIdent.Map.fold (fn (k, v, acc) => ValueIdent.Map.insert k (ModL v) acc) (#v e) (#v s)
        , t = TypeIdent.Map.fold (fn (k, v, acc) => TypeIdent.Map.insert k v acc) (#t e) (#t s)
        , tv = #tv e
        }
      )

    local
      structure S = U.Set
      val op@ = U.Lwd.append
      fun union l s = foldl (fn (v, acc) => S.insert v acc) s (U.Lwd.to_list l)
    in
      fun uvs ({m, s, v, t, ...} : t) =
      let
        fun fm k = ModuleIdent.Map.fold (fn (_, s, acc) => union (uvs_semsig s) acc) k m
        fun fs k = SignatureIdent.Map.fold (fn (_, asig, acc) => union (uvs_asig asig) acc) k s
        fun fv k =
          ValueIdent.Map.fold (fn (_, ModL(p, s), acc) => union (uvs_path p @ uvs_scheme s) acc 
                                | (_, CoreL _, acc) => acc) k v
        fun ft k = TypeIdent.Map.fold (fn (_, (ty, _), acc) => union (uvs_tycon ty) acc) k t
      in
        (ft o fv o fs o fm) S.empty
      end
    end

    structure Module = struct
      exception Unbound of module_ident

      fun lookup (e : t) id =
        valOf (ModuleIdent.Map.lookup id (#m e))
          handle Option => raise Unbound id

      fun insert id x (e : t) =
        { m = ModuleIdent.Map.insert id x (#m e)
        , s = #s e
        , v = #v e
        , t = #t e
        , tv = #tv e
        }
    end

    structure Signature = struct
      exception Unbound of signature_ident

      fun lookup (e : t) id =
        valOf (SignatureIdent.Map.lookup id (#s e))
          handle Option => raise Unbound id
    end

    structure Value = struct
      exception Unbound of value_ident

      datatype entry = datatype value_entry

      fun lookup (e : t) id =
        valOf (ValueIdent.Map.lookup id (#v e))
          handle Option => raise Unbound id

      fun insert id x (e : t) =
        { m = #m e
        , s = #s e
        , v = ValueIdent.Map.insert id x (#v e)
        , t = #t e
        , tv = #tv e
        }
    end

    structure Type = struct
      exception Unbound of type_ident

      fun lookup (e : t) id =
        valOf (TypeIdent.Map.lookup id (#t e))
          handle Option => raise Unbound id
    end

    structure TVar = struct
      exception Unbound of tvar

      fun lookup ({tv, ...} : t) id =
        valOf (T.lookup id tv)
          handle Option => raise Unbound id

      fun insert id x (e : t) =
        { m = #m e
        , s = #s e
        , v = #v e
        , t = #t e
        , tv = T.insert id x (#tv e)
        }
    end
  end
end

type env = Env.t
