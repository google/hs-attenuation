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

-- | Representational subtyping relations and variance roles.

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Attenuation
         ( -- * Attenuation
           Attenuation, attenuate, coercible
         , trans, repr, coer
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
         ) where

import Control.Category (Category(..))
import Data.Bifunctor (Bifunctor)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Contravariant (Contravariant)
import Data.Kind (Constraint)
import Data.Profunctor (Profunctor)
import Data.Type.Coercion (Coercion(..), sym)
import qualified Data.Type.Coercion as Coercion
import Data.Type.Equality ((:~:)(..))
import Data.Void (Void)
import GHC.Exts (Any)

#if MIN_VERSION_base(4,15,0)
import Unsafe.Coerce (unsafeEqualityProof, UnsafeEquality(..))
#else
import Unsafe.Coerce (unsafeCoerce)
#endif

-- | @Attenuation a b@ is a unidirectional 'Coercion' from @a@ to @b@.
--
-- "Attenuate: reduce the force, effect, or value of."  An @Attenuation@ takes
-- a stronger, stricter type to a weaker, more lax type.  It's meant to sound a
-- bit like 'Coercion', while conveying that it weakens the type of its
-- argument.
--
-- This arises from newtypes that impose additional invariants on their
-- representations: if we define @Fin :: Nat -> Type@ as a newtype over 'Int',
-- such as in <https://hackage.haskell.org/package/fin-int fin-int>, then it's
-- safe to 'coerce' @Fin@s to 'Int's, and @Fin@s to other @Fin@s with larger
-- @Nat@ parameters, but not vice versa.
--
-- Within the module defining this @Fin@ type, we can obtain 'Coercible'
-- between any two @Fin@ types regardless of their roles, because their newtype
-- constructors are in scope, but if we've taken appropriate precautions
-- (namely not exporting the constructor), we can't obtain it outside the
-- module.  We can relax this and make the coercion "opt-in" by exporting it in
-- the form of a 'Coercion' with a scary name like @unsafeCoFin@, but this is
-- still error-prone.
--
-- Instead, we introduce a newtype wrapper around 'Coercion' which restricts it
-- to be used only in the forward direction, and carefully design its API so
-- that it can only be obtained under the appropriate circumstances.
--
-- @Attenuation a b@ can be seen as a witness that @a@ is, semantically and
-- representationally, a subtype of @b@: that is, any runtime object that
-- inhabits @a@ also inhabits @b@ without any conversion.  Note, however, that
-- we can't have a useful typeclass of this subtyping relation because all of
-- its instances would have to be specified individually: whereas 'Coercible'
-- is willing to invert or compose coercions implicitly because of GHC magic, a
-- subtyping class would not have that affordance.
newtype Attenuation a b = Attenuation (Coercion a b)
  deriving (Eq, Ord, Show)

instance Category Attenuation where
  id = coercible
  (.) = flip trans

-- | Coerce along an 'Attenuation'.
--
-- This is really, truly a coercion when it reaches Core.
attenuate :: Attenuation a b -> a -> b
attenuate (Attenuation Coercion) = coerce

-- | Any coercible types have an 'Attenuation'.
coercible :: Coercible a b => Attenuation a b
coercible = Attenuation Coercion

-- | Transitivity of 'Attenuation's.  See also the 'Category' instance.
trans :: Attenuation a b -> Attenuation b c -> Attenuation a c
trans (Attenuation coAB) (Attenuation coBC) =
  Attenuation (Coercion.trans coAB coBC)

-- | Any type is unidirectionally coercible to itself.
repr :: (a :~: b) -> Attenuation a b
repr Refl = Attenuation Coercion

-- | Bidirectional coercions can be weakened to unidirectional coercions.
coer :: Coercion a b -> Attenuation a b
coer = Attenuation

-- | A witness that @a@ occurs representationally in @s@ and that, when
-- substituting it for @b@, you get @t@.
--
-- These compose like Lenses from the "lens" package, so you can e.g. lift
-- 'Attenuation's through several @Functor@s by @'co'.co.co $ x@.
type Variance s t a b = Attenuation a b -> Attenuation s t

-- | A constraint that behaves like @type role f representational@.
--
-- This means that if we have this constraint in context and GHC can solve
-- 'Coercible' for some types @a@ and @b@, it will also lift the coercion to @f
-- a@ and @f b@.
type Representational f =
  (forall a b. Coercible a b => Coercible (f a) (f b) :: Constraint)

-- | Lift a 'Coercion' over a type constructor.
rep :: Representational f => Coercion a b -> Coercion (f a) (f b)
rep Coercion = Coercion

-- | A constraint that behaves like @type role f _ representational@.
--
-- See also 'Representational'.
type Representational1 f =
  (forall a b x. Coercible a b => Coercible (f x a) (f x b) :: Constraint)

-- | A constraint that behaves like @type role f representational _@.
--
-- See also 'Representational'.
type Representational0 f =
  (forall a b x. Coercible a b => Coercible (f a x) (f b x) :: Constraint)

-- | Lift a 'Coercion' over the last-but-one parameter of a type constructor.
rep0 :: Representational0 f => Coercion a b -> Coercion (f a x) (f b x)
rep0 Coercion = Coercion

-- | Lift an 'Attenuation' covariantly over a type constructor @f@.
--
-- Although we don't /use/ the 'Functor' constraint, it serves an important
-- purpose: to guarantee that the type parameter @a@ doesn't appear
-- contravariantly in @f a@; otherwise it'd be impossible to write a 'Functor'
-- instance.  This is used as a standin for more-detailed "covariant" and
-- "contravariant" type roles, which GHC doesn't have because there's no
-- built-in notion of subtyping to use them with.  'Representational1' provides
-- the actual lifting of coercions, and 'Functor' guarantees we've got the
-- variance right.
co :: (Functor f, Representational f) => Variance (f a) (f b) a b
co (Attenuation c) = Attenuation (rep c)

-- | Lift an 'Attenuation' contravariantly over a type constructor @f@.
--
-- Regarding the 'Contravariant' constraint, see 'co', and interchange mentions
-- of covariance and contravariance.
contra :: (Contravariant f, Representational f) => Variance (f b) (f a) a b
contra (Attenuation c) = Attenuation (sym $ rep c)

-- | Lift an 'Attenuation' covariantly over the left of a 'Bifunctor'.
--
-- Like with 'co' and 'contra', we require a not-actually-used constraint as
-- proof that the type has the appropriate variance.  Since there's not a
-- commonly-used class for functors over the last-but-one parameter, we use
-- 'Bifunctor'.  Sadly, this rules out types which are covariant in parameter
-- -1 and contravariant in parameter -0.
fstco :: (Bifunctor f, Representational0 f) => Variance (f a x) (f b x) a b
fstco (Attenuation c) = Attenuation (rep0 c)

-- | Lift an 'Attenuation' covariantly over the last-but-one type parameter.
--
-- Like with 'co' and 'contra', we require a not-actually-used constraint as
-- proof that the type has the appropriate variance.  Since there's not a
-- commonly-used class for functors over the last-but-one parameter, we use
-- 'Bifunctor'.  Sadly, this rules out types which are covariant in parameter
-- -1 and contravariant in parameter -0.
--
-- Note that any particular type with a @Bifunctor f@ instance should also have
-- @Functor (f x)@, so 'co' should work on any type that 'sndco' works on, but
-- in polymorphic contexts, the 'Functor' instance may not be available.
sndco :: (Bifunctor f, Representational1 f) => Variance (f x a) (f x b) a b
sndco (Attenuation c) = Attenuation (rep c)

-- | Lift an 'Attenuation' covariantly over the left of a 'Profunctor'.
--
-- Similarly to the use of 'Functor' in 'co', we use 'Profunctor' to guarantee
-- contravariance in the appropriate parameter.
lcontra :: (Profunctor p, Representational0 p) => Variance (p b x) (p a x) a b
lcontra (Attenuation c) = Attenuation (sym $ rep0 c)

-- | Lift an 'Attenuation' covariantly over the right of a 'Profunctor'.
--
-- Similarly to the use of 'Functor' in 'co', we use 'Profunctor' to guarantee
-- contravariance in the appropriate parameter.
--
-- As with 'sndco', this functions the same as 'co', but the needed 'Functor'
-- instance might not be available in polymorphic contexts.
rco :: (Profunctor p, Representational1 p) => Variance (p x a) (p x b) a b
rco (Attenuation c) = Attenuation (rep c)

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
