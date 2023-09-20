signature BTREE =
sig
  type 'a btree
  type key = int
  type 'a elem = key * 'a
  val empty : 'a btree
  val find : 'a btree * key -> 'a
  val insert : 'a btree * 'a elem -> 'a btree
(*
 val remove : 'a btree * key -> 'a btree
 val merge : 'a btree * 'a btree -> 'a btree
*)
end

(* BTree order is 3. *)
structure BTree: BTREE =
struct
  type key = int
  type 'a elem = key * 'a

  datatype 'a btree = Leaf
                    | Node of 'a btree *
                              'a elem option *
                              'a btree *
                              'a elem option *
                              'a btree

  val empty = Node (Leaf, NONE, Leaf, NONE, Leaf)

  fun find (Leaf, _) = raise Fail "No match"
    | find (Node (Leaf, NONE, Leaf, NONE, Leaf), _) = raise Fail "No match"
    | find (Node (b1, SOME (k1, v1), b2, NONE, Leaf), key) =
      if key < k1 then find (b1, key)
      else if key = k1 then v1
      else find (b2, key)
    | find (Node (b1, SOME (k1, v1), b2, SOME (k2, v2), b3), key) =
      if key < k1 then find (b1, key)
      else if key = k1 then v1
      else if key < k2 then find (b2, key)
      else if key = k2 then v2
      else find (b3, key)
    | find _ = raise Fail "Invalid BTree"

  fun insertWithOverflow (Node (Leaf, NONE, Leaf, NONE, Leaf), elem) =
      (NONE, Node (Leaf, SOME elem, Leaf, NONE, Leaf))
    | insertWithOverflow
        (Node (Leaf, e1 as SOME (k1, _), Leaf, NONE, Leaf), elem as (key, _)) =
      if key < k1 then (NONE, Node (Leaf, SOME elem, Leaf, e1, Leaf))
      else (NONE ,Node (Leaf, e1, Leaf, SOME elem, Leaf))
    | insertWithOverflow
        (Node (Leaf, e1 as SOME (k1, _), Leaf, e2 as SOME (k2, _), Leaf),
         elem as (key, _)) =
      let
        val (e1', e', e2') = if key < k1 then (SOME elem, e1, e2)
                             else if key < k2 then (e1, SOME elem, e2)
                             else (e1, e2, SOME elem)
        val node = Node (Leaf, e1', Leaf, NONE, Leaf)
        val overflowNode = Node (Leaf, e2', Leaf, NONE, Leaf)
      in
        (SOME (e', overflowNode), node)
      end
    | insertWithOverflow
        (Node (b1, e1 as SOME (k1, _), b2, NONE, Leaf), elem as (key, _)) =
      if key < k1 then
        let
          val (overflow, b1') = insertWithOverflow (b1, elem)
        in
          case overflow of
              NONE => (NONE, Node (b1', e1, b2, NONE, Leaf))
            | SOME (e', b') =>
              (NONE, Node (b1', e', b', e1, b2))
        end
      else
        let
          val (overflow, b2') = insertWithOverflow (b2, elem)
        in
          case overflow of
              NONE => (NONE, Node (b1, e1, b2', NONE, Leaf))
            | SOME (e', b') =>
              (NONE, Node (b1, e1, b2', e', b'))
        end
    | insertWithOverflow
        (Node (b1, e1 as SOME (k1, _), b2, e2 as SOME (k2, _), b3),
         elem as (key, _)) =
      if key < k1 then
        let
          val (overflow, b1') = insertWithOverflow (b1, elem)
        in
          case overflow of
              NONE => (NONE, Node (b1', e1, b2, e2, b3))
            | SOME (e', b') =>
              let val overflowNode = Node (b2, e2, b3, NONE, Leaf)
              in (SOME (e1, overflowNode), Node (b1', e', b', NONE, Leaf)) end
        end
      else if key < k2 then
        let
          val (overflow, b2') = insertWithOverflow (b2, elem)
        in
          case overflow of
              NONE => (NONE, Node (b1, e1, b2', e2, b3))
            | SOME (e', b') =>
              let val overflowNode = Node (b', e2, b3, NONE, Leaf)
              in (SOME (e', overflowNode), Node (b1, e1, b2', NONE, Leaf)) end
        end
      else
        let
          val (overflow, b3') = insertWithOverflow (b3, elem)
        in
          case overflow of
              NONE => (NONE, Node (b1, e1, b2, e2, b3'))
            | SOME (e', b') =>
              let val overflowNode = Node (b3', e', b', NONE, Leaf)
              in (SOME (e2, overflowNode), Node (b1, e1, b2, NONE, Leaf)) end
        end

    | insertWithOverflow _ = raise Fail "Invalid leaf"

  fun insert (btree, elem) =
      let
        val (overflowNode, btree') = insertWithOverflow (btree, elem)
      in
        case overflowNode of
            NONE => btree'
          | SOME (e', b') => Node (btree', e', b', NONE, Leaf)
      end
end
