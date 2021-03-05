structure Elaboration = struct
  open Syntax

  structure Quantified = Internal.Quantified

  structure List = struct
    open List

    fun without (xs, i) = (List.take (xs, i) @ List.drop (xs, i + 1))
  end

  exception EscapingLocalAbstractType of Internal.fvar
  exception NotAbstractType of Internal.tycon
  exception RefiningTypeOutsideSignature of type_ident location
  exception RefiningValueOutsideSignature of value_ident location
  exception IncludeFunctor of Internal.semsig
  exception ValueTypeConstructor of Internal.kind
  exception AppStructure of Internal.semsig
  exception CoreValueIdentitiy of value_ident
  exception NotBaseKind of Internal.kind

  infix |>
  fun x |> f = f x

  fun generalize env : Internal.tycon -> Internal.scheme = fn ty =>
  let
    open Internal

    val xs = Env.uvs env
    val ys = uvs_tycon ty

    val ys = U.Lwd.to_list (U.Set.fold (fn (x : U.t, acc) => U.Lwd.delete x acc) ys xs)

    val zs = map (fn u => (u, FVar.fresh KBase)) ys
    val () = app (fn ((_, r), fv) => r := Defined (Free fv)) zs
  in
    (List.length zs, close_tycon 0 (map #2 zs) ty)
  end

  fun elaborate_signature (env : env) : signature_ -> Internal.asig =
    fn SPath p =>
         let in
           case p of
                PIdent id => Env.Signature.lookup env id
              | PProj(m, id) =>
                  let
                    val Internal.Exist asig = #1 (elaborate_module env m)
                    fun f (ks, s) =
                    let
                      open Internal
                      val fvs = map FVar.fresh ks
                      val s' = open_semsig 0 (map Free fvs) s
                      val asig = Internal.proj_signature s' id
                      val () = find_asig fvs asig
                    in
                      asig
                    end
                  in
                    Quantified.apply f asig
                      handle Internal.Found fv => raise EscapingLocalAbstractType fv
                  end
         end
     | SSeq ds => Internal.Exist (Quantified.map Internal.Struct (elaborate_decls env ds))
     | SIArrow(id, x, y) =>
         let
           open Internal
           val Exist asig1 = elaborate_signature env x

           val (xs, s1) = Quantified.proj asig1
           val ks = map Quantified.Info.extract xs
           val fvs = map FVar.fresh ks
           val s1 = open_semsig 0 (map Free fvs) s1
           val env' = env |> Env.Module.insert id s1

           val asig2 = elaborate_signature env' y
           val arr = (close_semsig 0 fvs s1, close_asig 0 fvs asig2)
           val u = Quantified.quantify xs arr
         in
           Exist (Quantified.from_body (IArrow u))
         end
     | SPArrow(id, x, y) =>
         let
           open Internal
           val Exist asig1 = elaborate_signature env x

           val (xs, s1) = Quantified.proj asig1
           val ks = map Quantified.Info.extract xs
           val fvs = map FVar.fresh ks
           val s1 = open_semsig 0 (map Free fvs) s1
           val env' = env |> Env.Module.insert id s1

           val Exist asig2 = elaborate_signature env' y

           val (ys, s2) = Quantified.proj asig2
           val ys = map (Quantified.Info.map (Kind.lift ks)) ys
           val lks = map Quantified.Info.extract ys
           val fvs' = map FVar.fresh lks
           val s2 = open_semsig 0 (map (fn fv => app_list (Free fv) (map Free fvs)) fvs') s2

           val arr = (close_semsig 0 fvs s1, close_semsig 0 fvs s2)
           val u = Quantified.quantify xs arr
         in
           Exist (Quantified.quantify ys (close_semsig 0 fvs' (PArrow u)))
         end
     | SWhereType(x, loc, ty) =>
         let
           open Internal
           val Exist asig = elaborate_signature env x

           val (xs, s) = Quantified.proj asig
           val fvs = map (FVar.fresh o Quantified.Info.extract) xs
           val s = open_semsig 0 (map Free fvs) s

           val (ty1, k1) = proj_type_loc s loc
           val fvs' = map FVar.fresh (Kind.args k1)

           fun f (fv, ty) =
             case ty of
                  App(x, y) =>
                    ( x before unify y (Free fv) (FVar.get_kind fv)
                      handle _ => raise NotAbstractType ty
                    )
                | _ => raise NotAbstractType ty

           val ty1' = foldr f (reduce (app_list ty1 (map Free fvs'))) fvs'
         in
           case ty1' of
                Free fv =>
                  let in
                    case FVar.nth (fvs, fv) of
                         SOME i =>
                           let
                             val (ty, k) = elaborate_type env ty
                             val () = Kind.unify k k1
                           in
                             Quantified.quantify (List.without (xs, i))
                               (close_semsig 0 (List.without (fvs, i)) (subst_semsig [(fv, ty)] s))
                                 |> Exist
                           end
                       | NONE => raise RefiningTypeOutsideSignature loc
                  end
              | _ => raise NotAbstractType ty1'
         end
     | SWhereVal(x, loc, p) =>
         let
           open Internal
           val Exist asig = elaborate_signature env x

           val (xs, s) = Quantified.proj asig
           val fvs = map (FVar.fresh o Quantified.Info.extract) xs
           val s = open_semsig 0 (map Free fvs) s

           val (p1, scheme1) = proj_value_loc s loc
           val p1' = reduce (from_path p1)
         in
           case p1' of
                Free fv =>
                  let in
                    case FVar.nth (fvs, fv) of
                         SOME i =>
                           let
                             val (p2, scheme2) = elaborate_value_path env p
                             val () = is_instance_of scheme1 scheme2
                           in
                             Quantified.quantify (List.without (xs, i))
                               (close_semsig 0 (List.without (fvs, i)) (subst_semsig [(fv, from_path p2)] s))
                                 |> Exist
                           end
                       | NONE => raise RefiningValueOutsideSignature loc
                  end
              | _ => raise RefiningValueOutsideSignature loc
         end
     | SWhereModule(x, loc, m) =>
         let
           open Internal
           val Exist asig = elaborate_signature env x

           val (xs, s) = Quantified.proj asig
           val ys = map (fn i => (FVar.fresh (Quantified.Info.extract i), i)) xs
           val fvs = map #1 ys
           val mp = FVar.Map.from_list ys
           val s = open_semsig 0 (map Free fvs) s

           val s' = proj_module_loc s loc
           val fvs_lwd = fvs_semsig (FVar.Set.from_list fvs) s'
           val fvs' = FVar.Lwd.to_list fvs_lwd

           val s2 = elaborate_module_path env m

           val asig' =
             Quantified.quantify
               (map (fn fv => valOf (FVar.Map.lookup fv mp)) fvs')
               (close_semsig 0 fvs' s')
               |> Quantified.map_with_location (relative_location loc) (fn x => x)
               |> Exist

           val () = explicit_asig asig'

           val tys = match s2 asig'

           val s3 = subst_semsig (ListPair.zipEq (fvs', tys)) s

           val other_fvs = List.filter (fn (fv, _) => not (FVar.Lwd.member fv fvs_lwd)) ys
         in
           Exist (
             Quantified.quantify (map #2 other_fvs)
               (close_semsig 0 (map #1 other_fvs) s3)
           )
         end
     | SLike m =>
         let
           val s = elaborate_module_path env m
           val () = Internal.explicit_semsig s
         in
           Internal.Exist (Quantified.from_body s)
         end

  and elaborate_decls env : decl list -> Internal.struct_ Internal.existential =
    fn []      => Quantified.from_body Internal.empty_struct
     | d :: ds =>
         let
           open Internal

           val e1 = elaborate_decl env d
           val (xs, s1) = Quantified.proj e1
           val fvs = map (FVar.fresh o Quantified.Info.extract) xs
           val s1 = open_struct 0 (map Free fvs) s1

           val e2 = elaborate_decls (env |> Env.insert s1) ds
           val (ys, s2) = Quantified.proj e2
           val fvs' = map (FVar.fresh o Quantified.Info.extract) ys
           val s2 = open_struct 0 (map Free fvs') s2

           val s = close_struct 0 (fvs @ fvs') (disjoint_union s1 s2)
         in
           Quantified.quantify (xs @ ys) s
         end

  and elaborate_decl env : decl -> Internal.struct_ Internal.existential =
    fn DVal(id, (vs, ty)) =>
         let
           open Internal

           val xs = map (fn v => (v, FVar.fresh KBase)) vs
           val env = foldl (fn ((v, fv), acc) => acc |> Env.TVar.insert v fv) env xs
           val (ty, k) = elaborate_type env ty
           val () = Kind.get_base ValueTypeConstructor k
           val fvs = FVar.Lwd.to_list (fvs_tycon (FVar.Set.from_list (map #2 xs)) ty)

           val scheme = (List.length fvs, close_tycon 0 fvs ty)
         in
           Quantified.quantify1 KBase (Quantified.V id) (insert_value id (Path(Bound(0, 0)), scheme) empty_struct)
         end
     | DValTrans(id, p) =>
         let open Internal in
           Quantified.from_body (insert_value id (elaborate_value_path env p) empty_struct)
         end
     | DType(id, k) =>
         let
           open Internal
           val k = elaborate_kind k
         in
           Quantified.quantify1 k (Quantified.T id) (insert_type id (Bound(0, 0), k) empty_struct)
         end
     | DTypeTrans(id, ty) =>
         let
           open Internal
           val (ty, k) = elaborate_type env ty
         in
           Quantified.from_body (insert_type id (ty, k) empty_struct)
         end
     | DModule(id, s) =>
         let
           open Internal
           val Exist asig = elaborate_signature env s
           fun f (mids, tid) = SOME (id :: mids, tid)
         in
           Quantified.map_with_location f (fn s => insert_module id s empty_struct) asig
         end
     | DModuleTrans(id, m) =>
         let
           open Internal
           val s = elaborate_module_path env m
           val () = explicit_semsig s
         in
           Quantified.from_body (insert_module id s empty_struct)
         end
     | DSignature(id, s) =>
         let
           open Internal
           val asig = elaborate_signature env s
         in
           Quantified.from_body (insert_signature id asig empty_struct)
         end
     | DInclude s =>
         let
           open Internal
           val Exist asig = elaborate_signature env s
         in
           Quantified.map (get_structure IncludeFunctor) asig
         end

  and elaborate_module_path env : module -> Internal.semsig = fn m =>
  let
    open Internal
    val (Exist asig, _) = elaborate_module env m
    val (xs, s) = Quantified.proj asig
    val fvs = map (FVar.fresh o Quantified.Info.extract) xs
    val s = open_semsig 0 (map Free fvs) s
    val () = find_semsig fvs s
      handle Internal.Found fv => raise EscapingLocalAbstractType fv
  in
    s
  end

  and elaborate_module env : module -> Internal.asig * Internal.purity =
    fn MPath p =>
         let in
           case p of
                PIdent id =>
                  (Internal.Exist(Quantified.from_body (Env.Module.lookup env id)), Internal.Pure)
              | PProj(m, id) =>
                  let
                    val (Internal.Exist asig, p) = elaborate_module env m
                    fun f (ids, id') =
                      case ids of
                           [] => NONE
                         | x :: xs =>
                             if ModuleIdent.equal x id
                             then SOME(xs, id')
                             else NONE
                  in
                    ( Internal.Exist (Quantified.map_with_location f (fn s => Internal.proj_module s id) asig)
                    , p
                    )
                  end
         end
     | MSeq bs =>
         let val (e, purity) = elaborate_bindings env bs in
           (Internal.Exist (Quantified.map Internal.Struct e), purity)
         end
     | MAbs(id, s1, x) =>
         let
           open Internal
           val Exist asig1 = elaborate_signature env s1

           val (xs, s1) = Quantified.proj asig1
           val ks = map Quantified.Info.extract xs
           val fvs = map FVar.fresh ks
           val s1 = open_semsig 0 (map Free fvs) s1
           val env = env |> Env.Module.insert id s1

           val (Exist asig2, purity) = elaborate_module env x
         in
           case purity of
                Impure =>
                  let
                    val u =
                      Quantified.quantify xs (close_semsig 0 fvs s1, close_asig 0 fvs (Exist asig2))
                  in
                    (Exist (Quantified.from_body (IArrow u)), Pure)
                  end
              | Pure =>
                  let
                    val (ys, s2) = Quantified.proj asig2
                    val ys = map (Quantified.Info.map (Kind.lift ks)) ys
                    val lks = map Quantified.Info.extract ys
                    val fvs' = map FVar.fresh lks
                    val s2 = open_semsig 0 (map (fn fv => app_list (Free fv) (map Free fvs)) fvs') s2

                    val arr =
                      PArrow (Quantified.quantify xs (close_semsig 0 fvs s1, close_semsig 0 fvs s2))
                  in
                    (Exist (Quantified.quantify ys (close_semsig 0 fvs' arr)), Pure)
                  end
         end
     | MApp(id1, id2) =>
         let
           val s1 = Env.Module.lookup env id1
           val (u, purity) = Internal.get_functor AppStructure s1
           val s2 = Env.Module.lookup env id2
           val tys = Internal.match s2 (Internal.Exist (Quantified.map (fn (dom, _) => dom) u))
         in
           (Internal.open_asig 0 tys (#2 (Quantified.get_body u)), purity)
         end
     | MSeal(id, s) =>
         let
           open Internal
           val s1 = Env.Module.lookup env id
           val asig2 = elaborate_signature env s
           val _ = match s1 asig2
         in
           (asig2, Pure)
         end
     | MUnpack(e, s) =>
         let
           open Internal
           val ty = elaborate_term env e
           val asig = elaborate_signature env s
           val () = unify ty (Pack (norm_asig asig)) KBase
         in
           (asig, Impure)
         end

  and elaborate_bindings env : binding list -> Internal.struct_ Internal.existential * Internal.purity =
    fn []      => (Quantified.from_body Internal.empty_struct, Internal.Pure)
     | b :: bs =>
         let
           open Internal
           val (e1, purity1) = elaborate_binding env b
           val (xs, s1) = Quantified.proj e1
           val fvs = map (FVar.fresh o Quantified.Info.extract) xs
           val s1 = open_struct 0 (map Free fvs) s1

           val (e2, purity2) = elaborate_bindings (env |> Env.insert s1) bs
           val (ys, s2) = Quantified.proj e2
           val fvs' = map (FVar.fresh o Quantified.Info.extract) ys
           val s2 = open_struct 0 (map Free fvs') s2

           val s = close_struct 0 (fvs @ fvs') (union s1 s2)

           fun f loc =
             case loc of
                  (mid :: _, _)          => ModuleIdent.Map.member mid (#m s2)
                | ([], Quantified.T tid) => TypeIdent.Map.member tid (#t s2)
                | ([], Quantified.V vid) => ValueIdent.Map.member vid (#v s2)

           val zs = map (Quantified.Info.make_obsolete f) xs @ ys
         in
           (Quantified.quantify zs s, join purity1 purity2)
         end

  and elaborate_binding env : binding -> Internal.struct_ Internal.existential * Internal.purity =
    fn BVal(id, e) =>
         let open Internal in
           case e of
                VPath p =>
                  let in
                    case p of
                         PIdent id' =>
                           let in
                             case Env.Value.lookup env id' of
                                  Env.Value.ModL x =>
                                    (Quantified.from_body (insert_value id x empty_struct), Pure)
                                | Env.Value.CoreL ty =>
                                    ( Quantified.quantify1 KBase (Quantified.V id)
                                        (insert_value id (Path(Bound(0, 0)), (0, ty)) empty_struct)
                                    , Pure
                                    )
                           end
                       | PProj(m, id') =>
                           let
                             val (Exist asig, purity) = elaborate_module env m
                             fun f s = insert_value id (proj_value s id') empty_struct
                           in
                             (Quantified.map f asig, purity)
                           end
                  end
              | _ =>
                  let
                    val ty = elaborate_term env e
                    val scheme = generalize env ty
                    val x = (Path(Bound(0, 0)), scheme)
                    val s = insert_value id x empty_struct
                  in
                    (Quantified.quantify1 KBase (Quantified.V id) s, Pure)
                  end
         end
     | BType(id, ty) =>
         let
           open Internal
           val (ty, k) = elaborate_type env ty
         in
           (Quantified.from_body (insert_type id (ty, k) empty_struct), Pure)
         end
     | BModule(id, m) =>
         let
           open Internal
           val (Exist asig, purity) = elaborate_module env m
           fun f (mids, tid) = SOME (id :: mids, tid)
         in
           ( Quantified.map_with_location f (fn s => insert_module id s empty_struct) asig
           , purity
           )
         end
     | BSignature(id, s) =>
         let
           open Internal
           val asig = elaborate_signature env s
         in
           ( Quantified.from_body (insert_signature id asig empty_struct)
           , Pure
           )
         end
     | BInclude m =>
         let
           open Internal
           val (Exist asig, purity) = elaborate_module env m
         in
           (Quantified.map (get_structure IncludeFunctor) asig, purity)
         end

  and elaborate_type env : tycon -> Internal.tycon * Internal.kind =
    fn TPath p =>
         let in
           case p of
                PIdent id => Env.Type.lookup env id
              | PProj(m, id) =>
                  let
                    val Internal.Exist asig = #1 (elaborate_module env m)
                    fun f (ks, s) =
                    let
                      open Internal
                      val fvs = map FVar.fresh ks
                      val s' = open_semsig 0 (map Free fvs) s
                      val (ty, k) = Internal.proj_type s' id
                      val () = find_tycon fvs ty
                    in
                      (ty, k)
                    end
                  in
                    Quantified.apply f asig
                      handle Internal.Found fv => raise EscapingLocalAbstractType fv
                  end
         end
     | TPack s =>
         (Internal.Pack (Internal.norm_asig (elaborate_signature env s)), Internal.KBase)
     | TVar v =>
         let val fv = Env.TVar.lookup env v in
           (Internal.Free fv, Internal.FVar.get_kind fv)
         end
     | TAbs(v, x) =>
         let
           val fv = Internal.FVar.fresh Internal.KBase
           val (ty, k) = elaborate_type (env |> Env.TVar.insert v fv) x
         in
           (Internal.abs_list [fv] ty, Internal.KArrow(Internal.KBase, k))
         end
     | TApp(x, y) =>
         let
           open Internal
           val (ty1, k1) = elaborate_type env x
           val (k11, k12) = Kind.get_arrow k1
           val (ty2, k2) = elaborate_type env y
           val () = Kind.unify k11 k2
         in
           (App(ty1, ty2), k12)
         end
     | TArrow(x, y) =>
         let
           open Internal
           val (ty1, k1) = elaborate_type env x
           val () = Kind.get_base NotBaseKind k1
           val (ty2, k2) = elaborate_type env y
           val () = Kind.get_base NotBaseKind k2
         in
           (Arrow(ty1, ty2), KBase)
         end
     | TProd(x, y) =>
         let
           open Internal
           val (ty1, k1) = elaborate_type env x
           val () = Kind.get_base NotBaseKind k1
           val (ty2, k2) = elaborate_type env y
           val () = Kind.get_base NotBaseKind k2
         in
           (Prod(ty1, ty2), KBase)
         end
     | TSum(x, y) =>
         let
           open Internal
           val (ty1, k1) = elaborate_type env x
           val () = Kind.get_base NotBaseKind k1
           val (ty2, k2) = elaborate_type env y
           val () = Kind.get_base NotBaseKind k2
         in
           (Sum(ty1, ty2), KBase)
         end

  and elaborate_kind KBase      = Internal.KBase
    | elaborate_kind (KArrow k) = Internal.KArrow(Internal.KBase, elaborate_kind k)

  (* The generic version for (S-WHERE-VAL) and (D-VAL-EQ). Not appropriate for (E-PATH). *)
  and elaborate_value_path env : value_ident path -> Internal.path * Internal.scheme =
    fn PIdent id =>
         let in
           case Env.Value.lookup env id of
                Env.Value.ModL x  => x
              | Env.Value.CoreL _ => raise CoreValueIdentitiy id
         end
     | PProj(m, id) =>
         let
           open Internal
           val Exist asig = #1 (elaborate_module env m)
           fun f (ks, s) =
           let
             val fvs = map FVar.fresh ks
             val s' = open_semsig 0 (map Free fvs) s
             val (p, scheme) = proj_value s' id
             val () = find_path fvs p
             val () = find_scheme fvs scheme
           in
             (p, scheme)
           end
         in
           Quantified.apply f asig
             handle Internal.Found fv => raise EscapingLocalAbstractType fv
         end

  and elaborate_term env : term -> Internal.tycon =
    fn VPath p =>
         let in
           case p of
                PIdent id =>
                  let in
                    case Env.Value.lookup env id of
                         Env.Value.ModL(_, s) => Internal.instantiate s
                       | Env.Value.CoreL ty   => ty
                  end
              | PProj(m, id) =>
                  let
                    val Internal.Exist asig = #1 (elaborate_module env m)
                    fun f (ks, s) =
                    let
                      open Internal
                      val fvs = map FVar.fresh ks
                      val s' = open_semsig 0 (map Free fvs) s
                      val (_, scheme) = Internal.proj_value s' id
                      val () = find_scheme fvs scheme
                    in
                      instantiate scheme
                    end
                  in
                    Quantified.apply f asig
                      handle Internal.Found fv => raise EscapingLocalAbstractType fv
                  end
         end
     | VPack(m, s) =>
         let
           val (asig1, _) = elaborate_module env m
           val asig2 = elaborate_signature env s
           val () = Internal.subtype_asig asig1 asig2
         in
          Internal.Pack (Internal.norm_asig asig2)
         end
     | VAbs(id, x) =>
         let
           open Internal
           val ty1 = Unif(UVar.fresh (), ref Undefined)
           val env = env |> Env.Value.insert id (Env.Value.CoreL ty1)
           val ty2 = elaborate_term env x
         in
           Arrow(ty1, ty2)
         end
     | VApp(x, y) =>
         let
           open Internal
           val ty1 = elaborate_term env x
           val ty2 = elaborate_term env y
           val ty = Unif(UVar.fresh (), ref Undefined)
           val () = unify ty1 (Arrow(ty2, ty)) KBase
         in
           ty
         end
     | VUnit => Internal.Unit
     | _ => raise Fail "TODO"
end
