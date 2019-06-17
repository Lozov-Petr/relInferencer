open GT

open MiniKanren
open MiniKanrenStd
open Tester

open Syntax
open Inferencer
open Eval

let rec typ_reify x = For_typ.reify MiniKanren.reify typ_reify x

let rec typ_show x = show typ (show string) typ_show x

let rec ltyp_show x = show logic (show typ (show logic @@ show string) ltyp_show) x

let typ_run x = runR typ_reify typ_show ltyp_show x

(****************************************)

let rec pat_reify x = For_pat.reify
                        MiniKanren.reify
                        MiniKanren.reify
                        (List.reify pat_reify) x

let rec pat_show x = show pat
                        (show string)
                        (show string)
                        (show List.ground pat_show) x

let rec lpat_show x = (show logic @@ show pat
                        (show logic @@ show string)
                        (show logic @@ show string)
                        (show List.logic @@ lpat_show)) x

let rec expr_reify x = For_expr.reify
                        MiniKanren.reify
                        MiniKanren.reify
                        (List.reify expr_reify)
                        expr_reify
                        (List.reify @@ Pair.reify pat_reify expr_reify) x

let rec expr_show x = show expr
                        (show string)
                        (show string)
                        (show List.ground expr_show)
                        expr_show
                        (show List.ground @@ show Pair.ground pat_show expr_show) x

let rec lexpr_show x = (show logic @@ show expr
                        (show logic @@ show string)
                        (show logic @@ show string)
                        (show List.logic lexpr_show)
                        lexpr_show
                        (show List.logic @@ show Pair.logic lpat_show lexpr_show)) x

let expr_run x = runR expr_reify expr_show lexpr_show x

(****************************************)

let rec val_reify x = For_value.reify
                        MiniKanren.reify
                        MiniKanren.reify
                        expr_reify
                        (List.reify @@ Pair.reify MiniKanren.reify val_reify)
                        (List.reify val_reify) x

let rec val_show x = show value
                      (show string)
                      (show string)
                      expr_show
                      (show List.ground @@ show Pair.ground (show string) val_show)
                      (show List.ground val_show) x

let rec lval_show x = (show logic @@ show value
                       (show logic @@ show string)
                       (show logic @@ show string)
                       lexpr_show
                       (show List.logic @@ show Pair.logic (show logic @@ show string) lval_show)
                       (show List.logic lval_show)) x

let val_run x = runR val_reify val_show lval_show x

(****************************************)

let varX () = eVar !!"x"
let varY () = eVar !!"y"

let tTyp () = tBase !!"t"
let kTyp () = tBase !!"k"

let id () = eAbst !!"x" (eVar !!"x")

let tBool () = tBase !!"Bool"

let eTrue () = eCtor !!"true" (nil ())

let eFalse () = eCtor !!"false" (nil ())

let true_info () = ctor_info !!"true" (tBool ()) (nil ())
let false_info () = ctor_info !!"false" (tBool ()) (nil ())

let bool_info () = [true_info (); false_info ()]

let fnot () =
  eAbst !!"x" (
    eMatch (eVar !!"x") (List.list [
      pair (pCtor (!!"true")  (nil ())) (eFalse ());
      pair (pCtor (!!"false") (nil ())) (eTrue ());
    ])
  )

let tPair () = tBase !!"Pair"

let ePair a b = eCtor !!"pair" (a %< b)

let pair_info ta tb = ctor_info !!"pair" (tPair ()) (ta %< tb)

(****************************************)

let () =

  typ_run (-1) q qh ("'x' in []",
    fun q -> type_inferencero
      (nil ())
      (nil ())
      (varX ())
      q
  );

  typ_run (-1) q qh ("'x' in [x, t]",
    fun q -> type_inferencero
      (nil ())
      (pair !!"x" (tTyp ()) % nil ())
      (varX ())
      q
  );

  typ_run (-1) q qh ("'\\x -> x' in []",
    fun q -> type_inferencero
      (nil ())
      (nil ())
      (id ())
      q
  );

  typ_run (-1) q qh ("'(\\x -> x) x' in [x, t]",
    fun q -> type_inferencero
      (nil ())
      (pair !!"x" (tTyp ()) % nil ())
      (eApp (id ()) (varX ()))
      q
  );

  typ_run (-1) q qh ("'true' in []",
    fun q -> type_inferencero
      (List.list (bool_info ()))
      (nil ())
      (eTrue ())
      q
  );

  typ_run (-1) q qh ("'false' in []",
    fun q -> type_inferencero
      (List.list (bool_info ()))
      (nil ())
      (eFalse ())
      q
  );

  typ_run (-1) q qh ("'fnot' in []",
    fun q -> type_inferencero
      (List.list (bool_info ()))
      (nil ())
      (fnot ())
      q
  );

  typ_run (-1) q qh ("pair(x, x) in [x, t]",
    fun q -> type_inferencero
      (pair_info (tTyp ()) (tTyp ()) % nil ())
      (pair !!"x" (tTyp ()) % nil ())
      (ePair (varX ()) (varX ()))
      q
  );

  typ_run (-1) q qh ("pair(x, y) in [x, t]",
    fun q -> type_inferencero
      (pair_info (tTyp ()) (tTyp ()) % nil ())
      (pair !!"x" (tTyp ()) % nil ())
      (ePair (varX ()) (varY ()))
      q
  );

  typ_run (-1) q qh ("pair(x, x) in [x, t] with pair :: t -> k -> pair",
    fun q -> type_inferencero
      (pair_info (tTyp ()) (kTyp ()) % nil ())
      (pair !!"x" (tTyp ()) % nil ())
      (ePair (varX ()) (varX ()))
      q
  );

  (**********************************************)

  expr_run (1) q qh ("synthesize '\\x -> x'",
    fun q -> fresh (t)
      (type_inferencero
        (nil ())
        (nil ())
        q
        (tArrow t t)
      )
  );

  expr_run (0) q qh ("synthesize 'x'",
    fun q -> fresh (t)
      (type_inferencero
        (nil ())
        (nil ())
        q
        (tBase t)
      )
  );

  expr_run (1) q qh ("synthesize 'Bool -> Bool'",
    fun q -> fresh (t x a b)
      (q === eAbst x (eMatch (eVar x) (a %< b)))
      (type_inferencero
        (List.list (bool_info ()))
        (nil ())
        q
        (tArrow (tBool ()) (tBool ()))
      )
  );
  ()

(****************************************)
(****************************************)
(****************************************)

let add () =
  eAbst !!"x" (eAbst !!"y" (
    eMatch (eVar !!"x") (List.list [
      pair (pCtor !!"O" (nil ()))              (eVar !!"y");
      pair (pCtor !!"S" (pVar !!"a" % nil ())) (eCtor !!"S" (eApp (eApp (eVar !!"add") (eVar !!"a")) (eVar !!"y") % nil ()))
    ])
  ))

let rec int2enat n = if n = 0 then eCtor !!"O" (nil ())
                              else eCtor !!"S" (int2enat (n - 1) % nil ())

let rec int2vnat n = if n = 0 then vCtor !!"O" (nil ())
                              else vCtor !!"S" (int2vnat (n - 1) % nil ())

(****************************************)

let () =
  val_run (-1) q qh ("eval 'fun x -> x'",
    fun q ->
      evalo (nil ()) (id ()) q
    );

  val_run (-1) q qh ("eval '(fun x -> x) true'",
    fun q ->
      evalo (nil ()) (eApp (id ()) (eCtor !!"true" (nil ()))) q
    );

  val_run (-1) q qh ("eval 'not true'",
    fun q ->
      evalo (nil ()) (eApp (fnot ()) (eCtor !!"true" (nil ()))) q
    );

  expr_run (1) q qh ("eval 'Q true' 'false' /\\ eval 'Q false' 'true'",
    fun q ->
      evalo (nil ()) (eApp q (eCtor !!"true" (nil ()))) (vCtor !!"false" (nil ())) &&&
      evalo (nil ()) (eApp q (eCtor !!"false" (nil ()))) (vCtor !!"true" (nil ()))
    );

    expr_run (2) q qh ("eval 'Q O' 'O' /\\ eval 'Q (S O)' 'O'",
      fun q ->
        (evalo (nil ()) (eApp q (int2enat 0)) (int2vnat 0)) &&&
        (evalo (nil ()) (eApp q (int2enat 1)) (int2vnat 0)) &&&
        (evalo (nil ()) (eApp q (int2enat 2)) (int2vnat 1))
      );

  expr_run (10) q qh ("reeeeec",
    fun q -> fresh (a b c)
      (q === eAbst !!"x" (eAbst !!"y" (eMatch (eVar !!"x") (List.list [pair (pCtor !!"O" (nil ())) (eVar !!"y");
                                                                       pair (pCtor !!"S" (pVar !!"z" % nil ())) (eCtor !!"S" (eApp (eApp a b) c % nil ()))]))))
      (evalo (nil ()) (eApp (eAbst !!"add" (eApp (eApp (eVar !!"add") (int2enat 0)) (int2enat 0))) q) (int2vnat 0))
      (evalo (nil ()) (eApp (eAbst !!"add" (eApp (eApp (eVar !!"add") (int2enat 0)) (int2enat 1))) q) (int2vnat 1))
      (evalo (nil ()) (eApp (eAbst !!"add" (eApp (eApp (eVar !!"add") (int2enat 1)) (int2enat 0))) q) (int2vnat 1))
      (evalo (nil ()) (eApp (eAbst !!"add" (eApp (eApp (eVar !!"add") (int2enat 1)) (int2enat 1))) q) (int2vnat 2))
      (evalo (nil ()) (eApp (eAbst !!"add" (eApp (eApp (eVar !!"add") (int2enat 5)) (int2enat 4))) q) (int2vnat 9))
    );

  ()
