-- Copyright 2021 Google LLC
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

-- | Unsafe misuses of 'Attenuation's\' underlying 'Coercion's.
--
-- This can allow violating the invariants of the source type, since it allows
-- casting in the opposite direction from the intended 'Attenuation'.  If the
-- 'Coercion' is lifted to a 'Data.Coerce.Coercible' instance, this is
-- especially bad, since it can get used invisibly to allow lifted or composed
-- coercions that shouldn't be allowed.  The contract defined here is that
-- types may rely absolutely on 'Attenuation's not being used backwards in a
-- way that violates their internal invariants, including for type-safety and
-- memory-safety purposes.  As such, it is /unsafe/ to extract the 'Coercion'
-- from an 'Attenuation', and any nonsense that results from doing so
-- constitutes a bug in the client code that called 'unsafeToCoercion'.
--
-- This means extreme caution must be used with the contents of this module.
-- It's always safe to use this to cast values back to their original type or
-- to any type the original type is attenuable to.  Otherwise, the safety of a
-- particular backwards cast depends entirely on the specific types involved.
--
-- Take care not to hold onto / leak inverted 'Attenuation's or
-- illegitimately-obtained 'Coercion's by accident!

module Data.Type.Attenuation.Unsafe (unsafeToCoercion, unsafeSym) where

import Data.Type.Coercion (Coercion, sym)

import Data.Type.Attenuation.Internal (Attenuation(..))

-- | Unsafely access the internal 'Coercion' of an 'Attenuation'.
unsafeToCoercion :: Attenuation a b -> Coercion a b
unsafeToCoercion (Attenuation c) = c

-- | Unsafely invert an 'Attenuation'.
unsafeSym :: Attenuation a b -> Attenuation b a
unsafeSym (Attenuation c) = Attenuation (sym c)
