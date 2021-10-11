# 0.2.0

* Rename `attenuate` to `attenuateWith` (breaking change).
* Split `profunctors` features to a separate package (breaking change).
* Add an `Attenuable` class that does a decent job of deriving `Attenuation`s.
* Add a new `attenuate` that uses `Attenuable`.
* Add a `Data.Attenuation.Unsafe` module giving access to the internals.
* Add `HasDict` for `Attenuation` (with new enough `constraints`).
* Add `:-` entailments corresponding to pseudo-instances of `Attenuable`.

# 0.1.0.0

Added everything that exists in this version.  See Haddock documentation for a
complete accounting.
