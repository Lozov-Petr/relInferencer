open GT

open MiniKanren
open MiniKanrenStd
open Syntax
open Util

@type ('var, 'ctor, 'expr, 'env, 'args) value =
  | VClosure of 'var * 'expr * 'env
  | VCtor    of 'ctor * 'args with show

module For_value = (Fmap5)
  (struct
    let rec fmap fvar fctor fexpr fenv fargs = function
      | VClosure (var, expr, env) -> VClosure (fvar var, fexpr expr, fenv env)
      | VCtor  (ctor, args)       -> VCtor (fctor ctor, fargs args)
    type ('a, 'b, 'c, 'd, 'e) t = ('a, 'b, 'c, 'd, 'e) value
  end)

let vClosure var expr env = inj @@ For_value.distrib @@ VClosure (var, expr, env)
let vCtor ctor args       = inj @@ For_value.distrib @@ VCtor (ctor, args)

let rec matcho pat scr env env' = conde [
  fresh (x)
    (pat  === pVar x)
    (env' === some @@ pair x scr % env);

  fresh (ctor pats scrs patsAndScrs)
    (pat === pCtor ctor pats)
    (scr === vCtor ctor scrs)
    (zippo pats scrs patsAndScrs)
    (List.foldro
      (fun ps menv env' ->
        conde [
          (menv === none ()) &&& (env' === none ());
          fresh (env pat scr)
            (menv === some env)
            (ps === pair pat scr)
            (matcho pat scr env env')
        ])
      (some env) patsAndScrs env');

    fresh (ctor pats)
      (pat === pCtor ctor pats)
      (env' === none ())
      (conde [
        fresh (ctor' scrs)
          (ctor =/= ctor')
          (scr === vCtor ctor' scrs);
        fresh (var expr env'')
          (scr === vClosure var expr env'')
      ])
  ]

let rec match_armo env env' arms scr expr =
  fresh (pat arms' expr' env'')
    (arms === pair pat expr' % arms')
    (matcho pat scr env env'')
    (conde [
       (env'' === none ()) &&& match_armo env env' arms' scr expr;
       (env'' === some env') &&& (expr === expr')
    ])


let rec evalo env expr value = conde [
  fresh (x v)
    (expr === eVar x)
    (lookupo env x v)
    (conde [
      fresh (n a)
        (v === vCtor n a)
        (v === value);
      fresh (y b e)
        (v === vClosure y b e)
        (value === vClosure y b (pair x v % e))
    ]);
  fresh (name args vals)
    (expr === eCtor name args)
    (value === vCtor name vals)
    (List.mapo (evalo env) args vals);
  fresh (env' body arg arg' x body')
    (expr === eApp body arg)
    (evalo env body (vClosure x body' env'))
    (evalo env arg arg')
    (evalo (pair x arg' % env') body' value);
  fresh (x body)
    (expr === eAbst x body)
    (value === vClosure x body env);
  fresh (scr arms scr' env' expr')
    (expr === eMatch scr arms)
    (evalo env scr scr')
    (match_armo env env' arms scr' expr')
    (evalo env' expr' value)
  ]
