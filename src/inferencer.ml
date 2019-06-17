open MiniKanren
open MiniKanrenStd
open Syntax
open Util

let rec type_inferencero ctors env expr typ =

  let infero = type_inferencero ctors in

  let rec fordro_fun p env env' =
    fresh (pat typ)
      (p === pair pat typ)
      (pat_infero env env' pat typ)

  and pat_infero env env' pat tPat =
    conde [
      fresh (v)
        (pat === pVar v)
        (env' === (pair v tPat % env));

      fresh (name args argTypes argsAndTypes)
        (pat === pCtor name args)
        (List.membero ctors (ctor_info name tPat argTypes))
        (zippo args argTypes argsAndTypes)
        (List.foldro fordro_fun env argsAndTypes env')
    ] in

  let case_infero env tPat tExpr case =
    fresh (env' pat expr)
      (case === pair pat expr)
      (pat_infero env env' pat tPat)
      (infero env' expr tExpr)
  in

  conde [
    fresh (v)
      (expr === eVar v)
      (List.membero env (pair v typ));

    fresh (name args types)
      (expr === eCtor name args)
      (List.membero ctors (ctor_info name typ types))
      (List.mapo (infero env) args types);

    fresh (f arg tArg)
      (expr === eApp f arg)
      (infero env f (tArrow tArg typ))
      (infero env arg tArg);

    fresh (x body tX tBody)
      (expr === eAbst x body)
      (typ === tArrow tX tBody)
      (infero (pair x tX % env) body tBody);

    fresh (scr tScr cases c cs)
      (expr === eMatch scr cases)
      (cases === c % cs)
      (infero env scr tScr)
      (forallo (case_infero env tScr typ) cases)

  ]
