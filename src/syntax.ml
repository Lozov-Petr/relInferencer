open MiniKanren
open GT

(*

type ('var, 'constr) pat =
  | PVar    of 'var
  | PConstr of 'constr * ('var, 'constr) pat list

type ('var, 'constr) expr =
  | EVar    of 'var
  | EConstr of 'constr * ('var, 'constr) pat list
  | EApp    of ('var, 'constr) expr * ('var, 'constr) expr
  | EAbst   of 'var * ('var, 'constr) expr
  | EMatch  of ('var, 'constr) expr * (('var, 'constr) pat, ('var, 'constr) expr) list

*)

@type ('var, 'ctor, 'pat_list) pat =
  | PVar  of 'var
  | PCtor of 'ctor * 'pat_list with show

@type ('var, 'ctor, 'expr_list, 'expr, 'match_list) expr =
  | EVar   of 'var
  | ECtor  of 'ctor * 'expr_list
  | EApp   of 'expr * 'expr
  | EAbst  of 'var * 'expr
  | EMatch of 'expr * 'match_list with show

@type ('base, 'typ) typ =
  | TBase  of 'base
  | TArrow of 'typ * 'typ with show

module For_pat = (Fmap3)
  (struct
    let rec fmap fa fb fc = function
      | PVar    a    -> PVar (fa a)
      | PCtor (b, c) -> PCtor (fb b, fc c)
    type ('a, 'b, 'c) t = ('a, 'b, 'c) pat
  end)

let pVar  a   = inj @@ For_pat.distrib @@ PVar a
let pCtor b c = inj @@ For_pat.distrib @@ PCtor (b, c)

module For_expr = (Fmap5)
  (struct
    let rec fmap fa fb fc fd fe = function
      | EVar a          -> EVar (fa a)
      | ECtor (b, c)    -> ECtor (fb b, fc c)
      | EApp  (d1, d2)  -> EApp (fd d1, fd d2)
      | EAbst  (a, d)   -> EAbst  (fa a, fd d)
      | EMatch (d, e)   -> EMatch (fd d, fe e)
    type ('a, 'b, 'c, 'd, 'e) t = ('a, 'b, 'c, 'd, 'e) expr
  end)

let eVar   a     = inj @@ For_expr.distrib @@ EVar a
let eCtor  b c   = inj @@ For_expr.distrib @@ ECtor (b, c)
let eApp   d1 d2 = inj @@ For_expr.distrib @@ EApp (d1, d2)
let eAbst  a d   = inj @@ For_expr.distrib @@ EAbst (a, d)
let eMatch d e   = inj @@ For_expr.distrib @@ EMatch (d, e)

module For_typ = (Fmap2)
  (struct
    let rec fmap fa fb = function
      | TBase  a        -> TBase (fa a)
      | TArrow (b1, b2) -> TArrow (fb b1, fb b2)
    type ('a, 'b) t = ('a, 'b) typ
  end)

let tBase   a     = inj @@ For_typ.distrib @@ TBase a
let tArrow  b1 b2 = inj @@ For_typ.distrib @@ TArrow (b1, b2)


(***********************************)

type ('ctor, 'typ, 'typ_list) ctor_info =
  { name      : 'ctor
  ; typ       : 'typ
  ; arg_types : 'typ_list
  }

module For_ctor_info = (Fmap3)
  (struct
    let rec fmap fa fb fc info =
      { name      = fa info.name
      ; typ       = fb info.typ
      ; arg_types = fc info.arg_types
      }
    type ('a, 'b, 'c) t = ('a, 'b, 'c) ctor_info
  end)

let ctor_info name typ arg_types =
  inj @@ For_ctor_info.distrib @@ { name ; typ; arg_types }
