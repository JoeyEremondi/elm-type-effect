import List

--and x y = True

type Foo = Foo | Bar

{-
val = 
  let
    x = ((\y -> 
      case y of
        Bar -> 3) Foo)
  in 3
-}


--Check list cases

head (x::_) = x

maybeHead l = case l of
  [] -> Nothing
  (x::_) -> Just x

--Should fail
badHead = head []
--Should succeed
goodHead = head [1,2,3]

--Both should succeed, since the mabye version is total
emptyMaybeHead = maybeHead []
consMaybeHead = maybeHead [2,3,4]


map f l = case l of
  [] -> []
  (x::xs) -> (f x) :: (map f xs )

--This should succeed. I'm surprised it doesn't get poisoned
mappedHead = head <| map (\x -> x * x) [1,2,3] 

--This should fail
--TODO why doesn't this fail?
badMappedHead = head <| map (\x -> x * x) []


finiteIntFn x = case x of
  0 -> True
  1 -> False
  2 -> True
  90 -> False

--Should fail, but doesn't because of poisoning --TODO
badInt1 = finiteIntFn (3 + 4)

--Should fail
badInt2 = finiteIntFn (7)

goodInt1 = finiteIntFn (2)

poisonInt1 = finiteIntFn (1+1)

infIntFn x = case x of
  0 -> True
  1 -> False
  2 -> True
  90 -> False
  _ -> True

goodInt3 = infIntFn 7
goodInt4 = infIntFn 2

--Comparisons: LT, EQ, GR
--Shows that the different branches are unified
--But poisoned to Top --TODO
reverseComparison comp = case comp of
  LT -> GT
  GT -> LT

--This should succeed --TODO why doesn't it?
goodJoin1 comp = case (reverseComparison LT) of
  LT -> 3
  GT -> -3
  EQ -> 0

--This one should succeed, but doesn't due to poisoning
poisonJoin1 comp = case (reverseComparison LT) of
  LT -> 3
  GT -> -3

--This match is valid, but would require constant propogation to see that it is
--So it gets poisoned
poisonJoin2 comp = case (reverseComparison LT) of
  GT -> 3

--This one obviously should not succeed
badJoin 1 = case (reverseComparison LT) of
  LT -> 3