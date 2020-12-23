-- | A library for processing lists in BiGUL.

module Generics.BiGUL.Lib.List where

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib

import Data.Maybe (isJust, fromJust, catMaybes)
import Data.List (span)


-- | List alignment. Operating only on the sources satisfying the source condition,
--   and using the specified matching condition, 'align' finds for each view the first matching source
--   that has not been matched with previous views, and updates the source using the inner program.
--   If there is no matching source, one is created using the creation argument —
--   after creation, the created source should satisfy the source condition and
--   match with the view as determined by the matching condition.
--   For a source not matched with any view, the concealment argument is applied —
--   if concealment computes to @Nothing@, the source is deleted;
--   if concealment computes to @Just s'@, where @s'@ should not satisfy the source condition,
--   the source is replaced by @s'@.
align :: forall s v. (Show s, Show v)
      => (s -> Bool)       -- ^ source condition
      -> (s -> v -> Bool)  -- ^ matching condition
      -> BiGUL s v         -- ^ inner program
      -> (v -> s)          -- ^ creation
      -> (s -> Maybe s)    -- ^ concealment
      -> BiGUL [s] [v]
align p match b create conceal = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| _ |] [p| [] |] [d| |])
  , $(normal [| \(s:_) (v:_) -> p s && match s v |] [| \(s:_) -> p s |])
    ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = align p match b create conceal |])
  , $(adaptive [| \(s:_) [] -> p s |])
    ==> \ss _ -> let (prefix, remaining) = span p ss
                 in  catMaybes (map conceal prefix) ++ remaining
  , $(normal [| \(s:_) _ -> not (p s) |] [| \(s:_) -> not (p s) |])
    ==> $(update [p| _:xs |] [p| xs |] [d| xs = align p match b create conceal |])
  , $(adaptive [| \ss (v:_) -> isJust (findFirstMatch v ss) |])
    ==> \ss (v:_) -> uncurry (:) (fromJust (findFirstMatch v ss))
  , $(adaptiveSV [p| _ |] [| \(v:_) -> p (create v) |])
    ==> \ss (v:_) -> create v : ss
  ]
  where
    findFirstMatch :: v -> [s] -> Maybe (s, [s])
    findFirstMatch v []                        = Nothing
    findFirstMatch v (s:ss) | p s && match s v = Just (s, ss)
                            | otherwise        = do (s', ss') <- findFirstMatch v ss
                                                    return (s', s:ss')
