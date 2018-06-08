# Leibniz Scala Library

The Leibniz’ equality law states that if `a` and `b` are identical then they
must have identical properties. Leibniz’ original definition reads as follows:
```
a ≡ b = ∀ f .f a ⇔ f b
```
and can be proven to be equivalent to:
```
a ≡ b = ∀ f .f a → f b
```

This library provides an encoding of Leibniz' equality and other related
concepts in Scala. See my impromptu [LC 2018](https://alexknvl.com/docs/scalaz_summit_presentation.pdf) presentation for an overview.

### Witnesses
 * `Is[A, B]` (with a type alias to `A === B`) witnesses that types
   `A` and `B` are exactly the same.
 * Similarly, `IsK[A, B]` (with a type alias to `A =~= B`) witnesses
   that types `A[_]` and `B[_]` are exactly the same. Combinators exist that
   allow you to prove that `F[A] === F[B]` for any `F[_[_]]` or that
   `A[X] === B[X]` for any `X`.
 * `Leibniz[L, H, A, B]` witnesses that types `A` and `B` are the same
   and that they both are in between types `L` and `H`.
 * `Is[F, A, B]` witnesses type-equality for F-Bounded types.
 * `As[A, B]` witnesses that `A` is a subtype of `B`.
 * `As1[A, B]` witnesses that `A` is a subtype of `B` using existential types.
 * `Liskov[L, H, A, B]` is a bounded counterpart to `As[A, B]`.
 * `Constant[F]` witnesses that HKT `F` is a constant type lambda.
 * `Injective[F]` witnesses that HKT `F` is injective (not a constant type lambda :smiley:).
 * `Covariant[F]` witnesses that HKT `F` is covariant (constant or strictly covariant).
 * Ditto other typeclasses / propositional types in `variance` package.
 * See my impromptu [LC 2018](https://alexknvl.com/docs/scalaz_summit_presentation.pdf) presentation for an overview.

## Quick Start
```scala
resolvers += Resolver.bintrayRepo("alexknvl", "maven")
libraryDependencies += "com.alexknvl"  %%  "leibniz" % "0.10.0"
```

## License
Code is provided under the MIT license available at https://opensource.org/licenses/MIT,
as well as in the LICENSE file.
