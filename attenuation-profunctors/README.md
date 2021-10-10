# attenuation-profunctors

Attenuation support for `profunctors`.

## Overview

This package provides functions for lifting `Attenuation`s across
`Profunctor`s, along with entailments for obtaining the related instances.

This is in a separate package from the rest of `attenuation` because
`profunctors` is a very heavy dependency, and the core functionality doesn't
need it.
