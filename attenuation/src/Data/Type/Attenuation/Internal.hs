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

{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Attenuation.Internal
         ( Attenuation(..), Attenuable(..)
         , Variance, Representational, Representational0, Representational1
         , refl, trans, co, fstco, sndco, lcontra, rco, rep, rep0
         , withAttenuation
         ) where

import Prelude hiding ((.))

import Control.Category (Category(..))
import Data.Bifunctor (Bifunctor)
import Data.Coerce (Coercible)
import Data.Kind (Constraint, Type)
import Data.Type.Coercion (Coercion(..), sym)
import qualified Data.Type.Coercion as Coercion

#if MIN_VERSION_constraints(0, 11, 0)
import Data.Constraint (Dict(..), HasDict(..))
#endif
import Data.Profunctor (Profunctor)

-- | A constraint that behaves like @type role f representational@.
--
-- This means that if we have this constraint in context and GHC can solve
-- 'Coercible' for some types @a@ and @b@, it will also lift the coercion to @f
-- a@ and @f b@.
type Representational f =
  (forall a b. Coercible a b => Coercible (f a) (f b) :: Constraint)

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

-- | A witness that @a@ occurs representationally in @s@ and that, when
-- substituting it for @b@, you get @t@.
--
-- These compose like Lenses from the "lens" package, so you can e.g. lift
-- 'Attenuation's through several @Functor@s by @'co'.co.co $ x@.
type Variance s t a b = Attenuation a b -> Attenuation s t

-- | Lift a 'Coercion' over a type constructor.
rep :: Representational f => Coercion a b -> Coercion (f a) (f b)
rep Coercion = Coercion

-- | Lift a 'Coercion' over the last-but-one parameter of a type constructor.
rep0 :: Representational0 f => Coercion a b -> Coercion (f a x) (f b x)
rep0 Coercion = Coercion

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
-- safe to 'Data.Coerce.coerce' @Fin@s to 'Int's, and @Fin@s to other @Fin@s
-- with larger @Nat@ parameters, but not vice versa.
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

-- | Lift an 'Attenuation' covariantly over the left of a 'Bifunctor'.
--
-- Like with 'co' and 'Data.Type.Attenuation.contra', we require a
-- not-actually-used constraint as proof that the type has the appropriate
-- variance.  Since there's not a commonly-used class for functors over the
-- last-but-one parameter, we use 'Bifunctor'.  Sadly, this rules out types
-- which are covariant in parameter -1 and contravariant in parameter -0.
fstco :: (Bifunctor f, Representational0 f) => Variance (f a x) (f b x) a b
fstco (Attenuation c) = Attenuation (rep0 c)

-- | Lift an 'Attenuation' covariantly over the last-but-one type parameter.
--
-- Like with 'co' and 'Data.Type.Attenuation.contra', we require a
-- not-actually-used constraint as proof that the type has the appropriate
-- variance.  Since there's not a commonly-used class for functors over the
-- last-but-one parameter, we use 'Bifunctor'.  Sadly, this rules out types
-- which are covariant in parameter -1 and contravariant in parameter -0.
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

-- | Lift an 'Attenuation' to a constraint within a subexpression.
--
-- This is just specialization of 'withDict'; consider using that or
-- 'Data.Constraint.\\'.
withAttenuation :: Attenuation a b -> (Attenuable a b => r) -> r
withAttenuation (Attenuation Coercion) r = r

-- If all else fails, we can promote a Coercible instance.  Since this is
-- less-specific than any sensible instance and is overlappable, it'll never be
-- selected if we have any other option, so we won't incur Coercible
-- constraints needlessly.
instance {-# INCOHERENT #-} Coercible a b => Attenuable a b

-- A more-specific, less-demanding version of the previous instance.  This
-- exists to suppress the 'Functor' and 'Bifunctor' instances when the
-- parameter is equal on both sides, since letting those instances win would
-- introduce 'Representational' constraints that we don't actually need.
instance {-# INCOHERENT #-} Attenuable (a :: Type) a

#if MIN_VERSION_constraints(0, 11, 0)
instance HasDict (Attenuable a b) (Attenuation a b) where
  -- Some fairly neat trickery here: because we have the (incoherent) instance
  -- that demotes Coercible to Attenuable, and because Attenuation internally
  -- just holds a Coercion, which in turn is just a GADT constructor holding a
  -- Coercible instance, we can actually just unwrap everything (unsafely) to
  -- reify an Attenuation back to an Attenuable instance without making any
  -- assumptions about the representation of the Attenuable dictionary.
  evidence = (`withAttenuation` Dict)
#endif

-- Any covariant functor with representational role for its parameter is
-- representationally covariant.
--
-- Since this instance is incoherent (and thus overlappable), it'll be
-- suppressed by any more-specific instance, so you can write instances by hand
-- for 'Contravariant' functors.
--
-- The main downside is that, by default, GHC will assume that unary type
-- constructors should solve 'Attenuable' by looking for a 'Functor' instance,
-- which could lead to confusing type errors for any 'Contravariant's that
-- don't have specific instances.  Since the alternative is that any covariant
-- types that aren't aware of the @attenuation@ package (which, let's be
-- honest, is gonna be pretty much all of them) will have no instance
-- available, this seems worth the tradeoff.
instance {-# INCOHERENT #-} (Functor f, Representational f, Attenuable x y)
      => Attenuable (f x) (f y) where
  attenuation = co attenuation

-- Similarly to the 'Functor' instance, this assumes by default that binary
-- type constructors should be 'Bifunctor's.
--
-- As before, this doesn't prevent specific instances for e.g. 'Profunctor's,
-- but rather just defines what GHC will look for if there's not a
-- more-specific instance.
--
-- This is more specific than the 'Functor' instance, so unfortunately we'll
-- end up picking 'Bifunctor' in preference to 'Functor'.  In that case, either
-- just write a manual instance for the particular type constructor, or build
-- the 'Attenuation' manually with 'co'.
instance {-# INCOHERENT #-}
         ( Bifunctor f, Representational0 f, Representational1 f
         , Attenuable a c
         , Attenuable b d
         )
      => Attenuable (f a b) (f c d) where
  attenuation = fstco attenuation . sndco attenuation

instance (Attenuable c a, Attenuable b d)
      => Attenuable (a -> b) (c -> d) where
  attenuation = lcontra attenuation . rco attenuation

instance (Attenuable a a', Attenuable b b')
      => Attenuable (a, b) (a', b') where
  attenuation = fstco attenuation . sndco attenuation

instance (Attenuable a a', Attenuable b b', Attenuable c c')
      => Attenuable (a, b, c) (a', b', c') where
  attenuation = fst3 . fstco attenuation . sndco attenuation
   where
    fst3 :: Attenuation (a, b', c') (a', b', c')
    fst3 = case attenuation @a @a' of Attenuation Coercion -> attenuation

-- | Transitivity of 'Attenuation's.  See also the 'Category' instance.
trans :: Attenuation a b -> Attenuation b c -> Attenuation a c
trans (Attenuation coAB) (Attenuation coBC) =
  Attenuation (Coercion.trans coAB coBC)

-- | Any type is unidirectionally-coercible to itself.
refl :: Attenuation a a
refl = Attenuation Coercion

instance Category Attenuation where
  id = refl
  (.) = flip trans

-- | @Attenuable a b@ is satisfiable iff there exists an @'Attenuation' a b@.
--
-- Since an 'Attenuation' is unique for a given pair of types (as it's
-- internally just a wrapper around a 'Coercible' instance), any way of
-- obtaining an 'Attenuation' gives exactly the same result.  This means all
-- 'Attenuable' instances that /could/ exist for a pair of types are also
-- identical.  In turn, this means that even "incoherent" instances for
-- 'Attenuable' are actually coherent after all: any arbitrary choice of an
-- instance gives the same result.  As such, it's perfectly fine for instances
-- of 'Attenuable' to be marked @INCOHERENT@, as long as it results in good
-- instance resolution behavior.  This is used to provide some convenient
-- "fallback" instances filling in the (numerous) gaps in the set of specific
-- instances: specifically, automatic demotion of 'Coercible' to 'Attenuable';
-- and automatic lifting of 'Attenuable' across 'Functor's and 'Bifunctor's.
--
-- The word "satisfiable" in the first paragraph is chosen carefully: not all
-- instances that are satisfiable will be solved automatically by GHC.  One can
-- obtain 'Attenuable' instances by 'Data.Constraint.\\' or by an entailment
-- ('Data.Constraint.:-'), for some types that wouldn't be solved by any of the
-- "real" instances.  In particular, this is useful for compositions of
-- attenuations and for lifting attenuations across
-- 'Data.Functor.Contravariant.Contravariant's and 'Profunctor's.
--
-- Not all instances will be solved automatically by GHC
class Attenuable a b where
  attenuation :: Attenuation a b
  default attenuation :: Coercible a b => Attenuation a b
  attenuation = Attenuation Coercion
