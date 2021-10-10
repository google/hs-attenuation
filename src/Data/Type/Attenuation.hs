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

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Representational subtyping relations and variance roles.

module Data.Type.Attenuation
         ( -- * Attenuation
           Attenuation, type (:⊆:), attenuateWith, coercible
         , trans, repr, coer, iso, inst
           -- ** Representationality
         , Representational, Representational0, Representational1, Variance
           -- ** Functor and Contravariant
         , co, contra
           -- ** Bifunctor
         , fstco, sndco
           -- ** Profunctor
         , lcontra, rco
           -- ** Initial and Final Objects
         , attVoid, attAny
           -- * Attenuable
         , Attenuable(..), type (⊆), attenuate
         , withAttenuation
           -- ** Entailments
         , contravariance, profunctoriality, transitivity
         ) where

import Prelude hiding ((.))

import Control.Category (Category(..))
import Data.Coerce (Coercible, coerce)
import Data.Functor.Contravariant (Contravariant(..))
import Data.Type.Coercion (Coercion(..), sym)
import Data.Type.Equality ((:~:)(..), gcastWith)
import Data.Void (Void)
import GHC.Exts (Any)

import Data.Constraint ((:-)(Sub), Dict(..), withDict)
import Data.Profunctor (Profunctor)

#if MIN_VERSION_base(4,15,0)
import Unsafe.Coerce (unsafeEqualityProof, UnsafeEquality(..))
#else
import Unsafe.Coerce (unsafeCoerce)
#endif

import Data.Type.Attenuation.Internal

-- | An operator form of 'Attenuation', by analogy to (':~:').
type (:⊆:) = Attenuation

-- | Coerce along an 'Attenuation'.
--
-- This is really, truly a coercion when it reaches Core.
attenuateWith :: Attenuation a b -> a -> b
attenuateWith (Attenuation Coercion) = coerce

-- | Any coercible types have an 'Attenuation'.
coercible :: Coercible a b => Attenuation a b
coercible = Attenuation Coercion

-- | Any type is unidirectionally coercible to itself.
repr :: (a :~: b) -> Attenuation a b
repr eq = gcastWith eq refl

-- | Bidirectional coercions can be weakened to unidirectional coercions.
coer :: Coercion a b -> Attenuation a b
coer = Attenuation

-- | Lift an 'Attenuation' contravariantly over a type constructor @f@.
--
-- Regarding the 'Contravariant' constraint, see 'co', and interchange mentions
-- of covariance and contravariance.
contra :: (Contravariant f, Representational f) => Variance (f b) (f a) a b
contra (Attenuation c) = Attenuation (sym $ rep c)

-- | 'Attenuation's across type constructors can be instantiated.
--
-- This means 'Attenuation's across type constructors lift equality of type
-- parameters to 'Attenuation' of the applied result.
--
-- This is analogous to how @Coercible f g@ works.
inst :: Attenuation f g -> Attenuation (f x) (g x)
inst (Attenuation Coercion) = Attenuation Coercion

-- | 'Attenuation' of 'Void' to any type.
--
-- If you have 'Void' appearing covariantly in a type, you can replace it with
-- any other lifted type with a coercion, because the value can't contain any
-- non-bottom 'Void' values (there are none), and any value that /is/ bottom
-- can "work" (i.e. throw or fail to terminate) just as well at any other
-- lifted type.
--
-- For example, if you have a @[Doc Void]@ (from
-- <https://hackage.haskell.org/package/pretty pretty>), you know it doesn't
-- have any annotations (or they're errors), so you can use it as @[Doc a]@
-- without actually traversing the list and @Doc@ structure to apply
-- 'Data.Void.absurd' to all of the 'Void's.
attVoid :: forall a. Attenuation Void a
attVoid = Attenuation $
#if MIN_VERSION_base(4,15,0)
  case unsafeEqualityProof :: UnsafeEquality a Void of UnsafeRefl -> Coercion
#else
  (unsafeCoerce (Coercion :: Coercion a a) :: Coercion Void a)
#endif

-- | 'Attenuation' of any type to 'Any'.
--
-- Similarly to 'attVoid', you can weaken any type to 'Any' for free, since any
-- value is a valid value of type 'Any'.
attAny :: forall a. Attenuation a Any
attAny = Attenuation $
#if MIN_VERSION_base(4,15,0)
  case unsafeEqualityProof :: UnsafeEquality a Any of UnsafeRefl -> Coercion
#else
  (unsafeCoerce (Coercion :: Coercion a a) :: Coercion a Any)
#endif

-- | An operator form of 'Attenuable', by analogy to @(~)@.
type (⊆) = Attenuable

-- | Coerce from a representational subtype @a@ to its supertype @b@.
attenuate :: Attenuable a b => a -> b
attenuate = attenuateWith attenuation

-- | Lift an 'Attenuation' to a constraint within a subexpression.
--
-- This is just specialization of 'withDict'; consider using that or
-- 'Data.Constraint.\\'.
withAttenuation :: Attenuation a b -> (Attenuable a b => r) -> r
withAttenuation = withDict

-- Type inference aid for use in entailments: otherwise it's ambiguous what
-- 'Attenuation' we want to promote with 'withAttenuation'.
toDict :: Attenuation a b -> Dict (Attenuable a b)
toDict att = withAttenuation att Dict

-- | 'Contravariant' functors map attenuation contravariantly.
contravariance
  :: forall f a b
   . (Representational f, Contravariant f)
  => Attenuable a b :- Attenuable (f b) (f a)
contravariance = Sub (toDict (contra attenuation))

-- | 'Profunctor's functors map attenuations profunctorially.
profunctoriality
  :: forall p a b c d
   . (Representational0 p, Representational1 p, Profunctor p)
  => (Attenuable a c, Attenuable b d) :- Attenuable (p c b) (p a d)
profunctoriality = Sub (toDict (rco attenuation . lcontra attenuation))

-- | 'Attenuation's are transitive.
transitivity
  :: forall b a c. (Attenuable b c, Attenuable a b) :- Attenuable a c
transitivity = Sub (toDict $ attenuation @b @c . attenuation @a @b)

-- | If 'Attenuation's in both directions exist, they're actually a 'Coercion'.
iso :: Attenuation a b -> Attenuation b a -> Coercion a b
iso (Attenuation c) _ = c
