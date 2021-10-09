# Changelog for polysemy-check

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

