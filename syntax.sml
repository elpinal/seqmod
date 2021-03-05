structure Syntax = struct
  datatype kind
    = KBase
    | KArrow of kind

  datatype index
    = Fst
    | Snd

  (* Note: we prefer `module` to `module_ident path`. *)
  datatype 'a path
    = PIdent of 'a
    | PProj of module * 'a

  and module
    = MPath of module_ident path
    | MSeq of binding list
    | MAbs of module_ident * signature_ * module
    | MApp of module_ident * module_ident
    | MSeal of module_ident * signature_
    | MUnpack of term * signature_

  and binding
    = BVal of value_ident * term
    | BType of type_ident * tycon
    | BModule of module_ident * module
    | BSignature of signature_ident * signature_
    | BInclude of module

  and signature_
    = SPath of signature_ident path
    | SSeq of decl list
    | SIArrow of module_ident * signature_ * signature_
    | SPArrow of module_ident * signature_ * signature_
    | SWhereType of signature_ * type_ident location * tycon
    | SWhereVal of signature_ * value_ident location * value_ident path
    | SWhereModule of signature_ * module_ident location * module
    | SLike of module

  and decl
    = DVal of value_ident * scheme
    | DValTrans of value_ident * value_ident path
    | DType of type_ident * kind
    | DTypeTrans of type_ident * tycon
    | DModule of module_ident * signature_
    | DModuleTrans of module_ident * module
    | DSignature of signature_ident * signature_
    | DInclude of signature_

  and term
    = VPath of value_ident path
    | VPack of module * signature_
    | VAbs of value_ident * term
    | VApp of term * term
    | VUnit
    | VCaseUnit of term * term
    | VProd of term * term
    | VProj of index * term
    | VInj of index * term
    | VCaseSum of term * value_ident * term * value_ident * term

  and tycon
    = TPath of type_ident path
    | TPack of signature_
    | TVar of tvar
    | TAbs of tvar * tycon
    | TApp of tycon * tycon
    | TArrow of tycon * tycon
    | TProd of tycon * tycon
    | TSum of tycon * tycon

  withtype scheme = tvar list * tycon

  fun map_path f =
    fn PIdent x => PIdent (f x)
     | PProj(m, x) => PProj(m, f x)
end
