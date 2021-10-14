# Changelog for polysemy-check

## v0.5.0.0 (2021-10-14)

- Flattened the module structure of `Polysemy.Check.Arbitrary`.
- Fixed a bug where `arbitraryActionFromRowOfType` would return bottom.
- Added an `Arbitrary` instance for `Sem r a`.
- Added tests to prove all generators have a uniform distribution for actions.
- `prepropLaw` now prints the actions it ran before and after your test.
- Changed the orphan `Show` instances for standard Polysemy effects to more
    easily be used for testing coverage.
- Added a `Show` instance for `SomeEffOfType`.
- (Internal) Removed the `GArbitraryKTerm` class

## v0.4.0.0 (2021-10-12)

- `GArbitraryK` now supports actions that contain existential types.
- (Internal) Aggressively rewrote the `GArbitraryK` typeclass to make better use
    of `kind-generics`.

## v0.3.0.0 (2021-10-09)

- `prepropLaw` now synthesizes a monadic prelude and postlude to your laws, to
    ensure they hold under every context. The type has changed as a result.
- `prepropEquivalent` now allows you to produce a functor `f` result, so you can
    check equivalence of the underlying state as well.

## v0.2.0.0 (2021-10-09)

- Updated the signature of `prepropEquivalent` to take a `Proxy r`. This lets
    you bind the `r` type variable, and use it as an argument to
    `arbitraryAction` et al.

## v0.1.0.0 (2021-10-08)

- Released!

## Unreleased changes

