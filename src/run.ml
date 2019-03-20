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

let varX () = eVar !!"x"

let tTyp () = tBase !!"t"

let id () = eAbst !!"x" (eVar !!"x")

let tBool () = tBase !!"Bool"

let eTrue () = eCtor !!"true" (nil ())

let eFalse () = eCtor !!"false" (nil ())

let true_info () = ctor_info !!"true" (tBool ()) (nil ())
let false_info () = ctor_info !!"false" (tBool ()) (nil ())

let bool_info () = [true_info (); false_info ()]

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

  typ_run (-1) q qh ("test '\\x -> x' in []",
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
