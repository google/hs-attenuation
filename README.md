# attenuation

Uni-directional coercions, or representational subtyping relations.

[![Stack CI](https://github.com/google/hs-attenuation/actions/workflows/stack-ci.yml/badge.svg)](https://github.com/google/hs-attenuation/actions/workflows/stack-ci.yml)

## Disclaimer

This is not an officially supported Google product.

## Hackage Status

* [![attenuation](https://badgen.net/runkit/awpr/hackage/v/attenuation?icon=haskell&cache=600)](https://hackage.haskell.org/package/attenuation)
  ![Uploaded](https://badgen.net/runkit/awpr/hackage/t/attenuation?cache=600)
  ![Haddock](https://badgen.net/runkit/awpr/hackage/d/attenuation?cache=600)

## Overview

This package provides `Attenuation`s, which act as uni-directional coercions, or
representational subtyping relations.

Like `Coercion`s, these can be used directly to coerce between their type
parameters at zero runtime cost, or lifted to operate over "larger" types.

Unlike `Coercion`s, these can be used only in one direction, from a "weaker"
type to a "stronger" type.  Accordingly, they have additional restrictions on
lifting through type constructors: they must respect the variance (covariance or
contravariance) of the type being lifted.  Lifting an `Attenuation` covariantly
lets you coerce from, e.g., `[Fin n] -> [Int]`, but not vice versa; while
lifting contravariantly lets you coerce from e.g. `Op Bool Int -> Op Bool (Fin
n)`, but not vice versa.
