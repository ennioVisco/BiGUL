-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.InOut
-- Copyright   :  (C) 2013 Hugo Pacheco
-- License     :  BSD-style (see below)
-- Maintainer  :  Hugo Pacheco <hpacheco@nii.ac.jp>
-- Stability   :  provisional
--
-- Generic sums of products representation for algebraic data types
--
-- @
-- Copyright (c) 2013, National Institute of Informatics

-- All rights reserved.

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are
-- met:

--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.

--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.

--     * The names of contributors may not be used to endorse or promote
--       products derived from this software without specific prior
--       written permission.

-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-- @
----------------------------------------------------------------------------

module GHC.InOut where

import GHC.Generics


class (Generic a,ToFromRep (Rep a)) => InOut a where
  inn :: F a -> a
  out :: a -> F a

type family Flatten (f :: * -> *) :: *
type F a = Flatten (Rep a)

class ToFromRep (f :: * -> *) where
  fromRep :: f x -> Flatten f
  toRep :: Flatten f -> f x

type instance Flatten U1 = ()
type instance Flatten (K1 i c) = c
type instance Flatten (M1 i c f) = Flatten f
type instance Flatten (f :+: g) = Either (Flatten f) (Flatten g)
type instance Flatten (f :*: g) = (Flatten f,Flatten g)

instance ToFromRep U1 where
  fromRep U1 = ()
  toRep () = U1
instance ToFromRep (K1 i c) where
  fromRep (K1 c) = c
  toRep c = K1 c
instance ToFromRep f => ToFromRep (M1 i c f) where
  fromRep (M1 f) = fromRep f
  toRep x = M1 $ toRep x
instance (ToFromRep f,ToFromRep g) => ToFromRep (f :+: g) where
  fromRep (L1 f) = Left (fromRep f)
  fromRep (R1 g) = Right (fromRep g)
  toRep (Left x) = L1 (toRep x)
  toRep (Right y) = R1 (toRep y)
instance (ToFromRep f,ToFromRep g) => ToFromRep (f :*: g) where
  fromRep (f :*: g) = (fromRep f,fromRep g)
  toRep (f,g) = (toRep f :*: toRep g)

instance (Generic a,ToFromRep (Rep a)) => InOut a where
  inn = to . toRep
  out = fromRep . from
