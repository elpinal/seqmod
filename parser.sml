structure ParserError = struct
  exception UnexpectedEOF
  exception UnexpectedToken of Token.t
  exception DuplicateTVars of tvar
end

structure Parser = MakeParser (
  structure Streamable = StreamStreamable

  structure Arg = struct
    open Syntax
    open ParserError

    datatype terminal = datatype Token.t

    type string = string
    type left_ref = Token.left ref
    type tycon = tycon
    type module = module
    type term = term
    type type_variable = tvar
    type type_variables = TVar.Lwd.t
    type decl_list = decl list
    type binding_list = binding list
    type type_location = type_ident location
    type value_location = value_ident location
    type module_location = module_ident location
    type projs = string list
    type projs1 = string list * string
    type lpath = string path

    fun to_kind tvs = TVar.Lwd.foldr (fn (_, acc) => KArrow acc) KBase tvs

    fun to_scheme tvs x = (TVar.Lwd.to_list tvs, x)

    fun module_id x = x
    fun mapp (x, y) =
      case (x, y) of
           (MPath(PIdent id1), MPath(PIdent id2)) => MApp(id1, id2)
         | _ => raise Fail "unimplemented"
    fun mclassic_path (s, ss) =
      foldl (fn (s, acc) => MPath(PProj(acc, ModuleIdent.from_string s))) (MPath(PIdent(ModuleIdent.from_string s))) ss
    fun mproj (m, s, ss) =
      foldl (fn (s, acc) => MPath(PProj(acc, ModuleIdent.from_string s))) (MPath(PProj(m, ModuleIdent.from_string s))) ss
    fun mseal (m, s) =
      case m of
           MPath(PIdent id) => MSeal(id, s)
         | _ => raise Fail "unimplemented"
    val mstruct = MSeq
    fun mstruct_proj (bs, s, ss) =
      foldl (fn (s, acc) => MPath(PProj(acc, ModuleIdent.from_string s))) (MPath(PProj(MSeq bs, ModuleIdent.from_string s))) ss
    val munpack = MUnpack
    fun mabs (id, x, y) = MAbs(ModuleIdent.from_string id, x, y)

    fun path_ident s = MPath(PIdent (ModuleIdent.from_string s))
    fun path_struct bs = MSeq bs

    fun projs_nil () = []
    val projs_cons = op::
    fun projs1_cons (x, xs) =
      case xs of
           [] => ([], x)
         | y :: ys =>
             let val (ys, y) = projs1_cons (y, ys) in
               (x :: ys, y)
             end

    fun lprojs1_singleton x = ([], x)
    fun lprojs1_cons (x, (ys, z)) = (x :: ys, z)

    val binclude = BInclude
    fun bmodule (s, m) = BModule(ModuleIdent.from_string s, m)
    fun bsignature (s, x) = BSignature(SignatureIdent.from_string s, x)
    fun btype (s, tvs, x) =
      BType(TypeIdent.from_string s, TVar.Lwd.foldr (fn (tv, acc) => TAbs(tv, acc)) x tvs)
    fun bval (s, x) = BVal(ValueIdent.from_string s, x)

    fun empty_bindings () = []
    val cons_bindings = op::

    fun signature_id x = x
    val sstruct = SSeq
    fun siarrow (id, x, y) = SIArrow(ModuleIdent.from_string id, x, y)
    fun sparrow (id, x, y) = SPArrow(ModuleIdent.from_string id, x, y)
    fun sident s = SPath(PIdent (SignatureIdent.from_string s))
    fun spath (m, (ss, s)) =
      SPath(PProj(foldl (fn (s, acc) => MPath(PProj(acc, ModuleIdent.from_string s))) m ss, SignatureIdent.from_string s))
    fun swhere_type (x, loc, tvs, ty) = SWhereType(x, loc, TVar.Lwd.foldr TAbs ty tvs)
    fun swhere_val (x, loc, p) = SWhereVal(x, loc, map_path ValueIdent.from_string p)
    fun swhere_module (x, loc, m) = SWhereModule(x, loc, m)
    val slike = SLike

    val dinclude = DInclude
    fun dmodule (s, x) = DModule(ModuleIdent.from_string s, x)
    fun dmoduletrans (s, x) = DModuleTrans(ModuleIdent.from_string s, x)
    fun dsignature (s, x) = DSignature(SignatureIdent.from_string s, x)
    fun dtype (s, tvs) = DType(TypeIdent.from_string s, to_kind tvs)
    fun dtypetrans (s, tvs, x) =
      DTypeTrans(TypeIdent.from_string s, TVar.Lwd.foldr (fn (tv, acc) => TAbs(tv, acc)) x tvs)
    fun dval (s, tvs, x) = DVal(ValueIdent.from_string s, to_scheme tvs x)
    fun dvaltrans (s, x) = DValTrans(ValueIdent.from_string s, map_path ValueIdent.from_string x)

    fun empty_decls () = []
    val cons_decls = op::

    fun lpath_ident s = PIdent s
    fun lpath_path (m, (ss, s)) =
      PProj(foldl (fn (s, acc) => MPath(PProj(acc, ModuleIdent.from_string s))) m ss, s)

    fun term_id x = x
    val vapp = VApp
    fun vinl x = VInj(Fst, x)
    fun vinr x = VInj(Snd, x)
    fun vfst x = VProj(Fst, x)
    fun vsnd x = VProj(Snd, x)
    val vprod = VProd
    val vpack = VPack
    fun vunit () = VUnit
    fun vcaseunit (x, y) = VCaseUnit(x, y)
    fun vpath x = VPath(map_path ValueIdent.from_string x)
    fun vabs (id, x) = VAbs(ValueIdent.from_string id, x)

    fun quote_ident s = TVar.from_string s

    fun type_id x = x
    val tapp = TApp
    val tarrow = TArrow
    val tprod = TProd
    val tsum = TSum
    val tvar = TVar
    val tpack = TPack
    fun tpath x = TPath(map_path TypeIdent.from_string x)

    fun tvars_nil () = TVar.Lwd.empty
    fun tvars_cons (x, xs) =
      if TVar.Lwd.member x xs
      then raise DuplicateTVars x
      else TVar.Lwd.append (TVar.Lwd.singleton x, xs)

    fun type_location_ident s = ([], TypeIdent.from_string s)
    fun type_location_proj (s, (mids, tid)) = (ModuleIdent.from_string s :: mids, tid)

    fun value_location_ident s = ([], ValueIdent.from_string s)
    fun value_location_proj (s, (mids, tid)) = (ModuleIdent.from_string s :: mids, tid)

    fun module_location_ident s = ([], ModuleIdent.from_string s)
    fun module_location_proj (s, (mids, mid)) = (ModuleIdent.from_string s :: mids, mid)

    fun error (s : Token.t Stream.stream) =
    let open Stream in
      case front s of
           Nil        => UnexpectedEOF
         | Cons(t, _) => UnexpectedToken t
    end
  end
)
