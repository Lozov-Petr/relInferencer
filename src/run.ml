open GT

open MiniKanren
open MiniKanrenStd
open Tester

open Syntax
open Inferencer

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
