{-
Test file

Joseph Eremondi
UU# 4229924
APA Project 2
April 17, 2015
-}

import List

--and x y = True

type Foo = Foo | Bar | Baz

fooFun x = case x of
  Foo -> 20
  Bar -> 30

goodFooTest = (fooFun Foo) + (fooFun Bar)
badFooTest = (fooFun Foo) + (fooFun Baz)


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

--This could succeed, but gets poisoned, since map is based on Case
poisonMappedHead = head <| map (\x -> x * x) [1,2,3] 

--This should fail
badMappedHead = head <| map (\x -> x * x) []


finiteIntFn x = case x of
  0 -> True
  1 -> False
  2 -> True
  90 -> False

--Should fail
badInt1 = finiteIntFn (3 + 4)

--Should fail
badInt2 = finiteIntFn (7)

goodInt1 = finiteIntFn (2)

--Fails because of poisoning, we don't do constant propogation
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
--But poisoned to Top
reverseComparison comp = case comp of
  LT -> GT
  GT -> LT

--This should succeed: because we cover all cases, it can match against top
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
badJoin1 = case (reverseComparison LT) of
  LT -> 3


-- Nesting Data structures
complicatedMaybeList x = case x of
  Just ([Just ([], Just 3), Just ([3,4,5], Nothing) ]) -> 100
  Just (Nothing :: _) -> 200

--Should succeed: shows that we can match patterns arbitrarily deep
goodDeepMatch = let
    v1 = complicatedMaybeList <| Just ([Just ([], Just 3), Just ([3,4,5], Nothing) ])
    v2 = complicatedMaybeList <| Just ([Nothing, Just ([], Nothing )])
  in v1 + v2

--Fails because the above function can't take Nothing
badDeepMatch = let
    v1 = complicatedMaybeList <| Just ([Just ([], Just 3), Just ([3,4,5], Nothing) ])
    v2 = complicatedMaybeList <| Just ([Nothing, Just ([], Nothing )])
    v3 = complicatedMaybeList Nothing
  in v1 + v2 + v3


fromJust x = case x of
  Just y -> y

intFromJust x = case x of
  Just y -> y
  Nothing -> -99

--Shows that polyvariance works
higherOrderFromJust f x y = (f x) + (f y)

goodFromJust1 = higherOrderFromJust fromJust (Just 3) (Just 4)

goodFromJust2 = higherOrderFromJust intFromJust (Just 3) Nothing

badFromJust =   higherOrderFromJust fromJust (Just 3) Nothing
