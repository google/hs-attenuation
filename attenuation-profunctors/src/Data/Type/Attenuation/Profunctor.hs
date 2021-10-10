-- Copyright 2020-2021 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}

-- | 'Attenuation's for 'Profunctor's.

module Data.Type.Attenuation.Profunctor
         ( -- * Profunctor Attenuations
           lcontra, rco, profunctoriality
         ) where

import Prelude hiding ((.))

import Control.Category ((.))

import Data.Constraint ((:-)(Sub), Dict(..))
import Data.Profunctor (Profunctor)
import Data.Type.Attenuation
         ( Attenuation, Attenuable
         , Variance, Representational0, Representational1
         , coer, attenuation, withAttenuation
         )
import Data.Type.Attenuation.Internal (Attenuation(..), rep0, rep)
import Data.Type.Coercion (sym)

-- | Lift an 'Attenuation' covariantly over the left of a 'Profunctor'.
--
-- Similarly to the use of 'Functor' in 'co', we use 'Profunctor' to guarantee
-- contravariance in the appropriate parameter.
lcontra :: (Profunctor p, Representational0 p) => Variance (p b x) (p a x) a b
lcontra (Attenuation c) = coer (sym $ rep0 c)

-- | Lift an 'Attenuation' covariantly over the right of a 'Profunctor'.
--
-- Similarly to the use of 'Functor' in 'co', we use 'Profunctor' to guarantee
-- contravariance in the appropriate parameter.
--
-- As with 'sndco', this functions the same as 'co', but the needed 'Functor'
-- instance might not be available in polymorphic contexts.
rco :: (Profunctor p, Representational1 p) => Variance (p x a) (p x b) a b
rco (Attenuation c) = coer (rep c)

-- Type inference aid for use in entailments: otherwise it's ambiguous what
-- 'Attenuation' we want to promote with 'withAttenuation'.
toDict :: Attenuation a b -> Dict (Attenuable a b)
toDict att = withAttenuation att Dict

-- | 'Profunctor's map attenuations profunctorially.
profunctoriality
  :: forall p a b c d
   . (Representational0 p, Representational1 p, Profunctor p)
  => (Attenuable a c, Attenuable b d) :- Attenuable (p c b) (p a d)
profunctoriality = Sub (toDict (rco attenuation . lcontra attenuation))
