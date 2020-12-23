-- | The unsafe interpreters, which assume that computation always succeeds and omit all dynamic checking.
--   Use these interpreters only when you have ensured that your 'Generics.BiGUL.BiGUL' program is correct.

module Generics.BiGUL.Interpreter.Unsafe (put, get, plainPut, plainGet) where

import Generics.BiGUL
import Generics.BiGUL.PatternMatching


fromRight :: Either a b -> b
fromRight (Right b) = b
fromRight _         = error "fromRight fails"

-- | The unsafe putback semantics of a 'Generics.BiGUL.BiGUL' program.
--   Execution either produces a |Just|-value or fails (possibly non-terminatingly).
put :: BiGUL s v -> s -> v -> Maybe s
put b s v = Just (plainPut b s v)

-- | The unsafe putback semantics of a 'Generics.BiGUL.BiGUL' program, as a pure (but partial) function.
plainPut :: BiGUL s v -> s -> v -> s
plainPut (Skip f)         s       v       = s
plainPut  Replace         s       v       = v
plainPut (l `Prod` r)     (s, s') (v, v') = (plainPut l s v, plainPut r s' v')
plainPut (RearrS p e b)   s       v       = let env = fromRight (deconstruct p s)
                                                m   = eval e env
                                                s'  = plainPut b m v
                                                con = fromRight (uneval p e s' (emptyContainer p))
                                            in  construct p (fromContainerS p env con)
plainPut (RearrV p e b)   s       v       = let v' = fromRight (deconstruct p v)
                                                m  = eval e v'
                                            in  plainPut b s m
plainPut (Dep f b)        s       (v, v') = plainPut b s v
plainPut (Case bs)        s       v       = putCase bs s v
plainPut (l `Compose` r)  s       v       = let m  = plainGet l s
                                                m' = plainPut r m v
                                            in  plainPut l s m'
plainPut (Checkpoint _ b) s       v       = plainPut b s v

getCaseBranch :: (s -> v -> Bool, CaseBranch s v) -> s -> Maybe v
getCaseBranch (p , Normal b q) s =
  if q s
  then let v = plainGet b s
       in  if p s v then Just v else Nothing
  else Nothing
getCaseBranch (p , Adaptive f) s = Nothing

putCaseWithAdaptation :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> (s -> s) -> s
putCaseWithAdaptation (pb@(p, b):bs) s v cont =
  if p s v
  then case b of
         Normal b q -> plainPut b s v
         Adaptive f     -> cont (f s v)
  else putCaseWithAdaptation bs s v cont

putCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> s
putCase bs s v = putCaseWithAdaptation bs s v (\s' -> putCase bs s' v)

-- | The unsafe get semantics of a 'Generics.BiGUL.BiGUL' program.
--   Execution either produces a |Just|-value or fails (possibly non-terminatingly).
get :: BiGUL s v -> s -> Maybe v
get b s = Just (plainGet b s)

-- | The unsafe get semantics of a 'Generics.BiGUL.BiGUL' program, as a pure (but partial) function.
plainGet :: BiGUL s v -> s -> v
plainGet (Skip f)         s       = f s
plainGet  Replace         s       = s
plainGet (l `Prod` r)     (s, s') = (plainGet l s, plainGet r s')
plainGet (RearrS p e b)   s       = let env = fromRight (deconstruct p s)
                                        m   = eval e env
                                    in  plainGet b m
plainGet (RearrV p e b)   s       = let v'  = plainGet b s
                                        con = fromRight (uneval p e v' (emptyContainer p))
                                        env = fromRight (fromContainerV p con)
                                    in  construct p env
plainGet (Dep f b)        s       = let v = plainGet b s in (v, f v)
plainGet (Case bs)        s       = getCase bs s
plainGet (l `Compose` r)  s       = let m = plainGet l s in plainGet r m
plainGet (Checkpoint _ b) s       = plainGet b s

getCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v
getCase (pb@(p, b):bs) s =
  case getCaseBranch pb s of
    Just v  -> v
    Nothing -> getCase bs s
