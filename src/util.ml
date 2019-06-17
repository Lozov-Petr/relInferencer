open MiniKanren
open MiniKanrenStd

let rec forallo p l =
  conde [
    l === nil ();

    fresh (x xs)
      (l === x % xs)
      (p x)
      (forallo p xs)
  ]

let rec zippo l1 l2 l =
  conde [
    (l1 === nil ()) &&& (l2 === nil ()) &&& (l === nil ());
    fresh (x xs y ys ls)
      (l1 === x % xs)
      (l2 === y % ys)
      (l === pair x y % ls)
      (zippo xs ys ls)
  ]

let rec lookupo l k v =
  fresh (k' v' l')
    (l === pair k' v' % l')
    (conde [
      (k === k') &&& (v === v');
      (k =/= k') &&& lookupo l' k v
    ])
