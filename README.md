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
concepts in Scala.

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
 ---
 * `Exists[F[_]]` witnesses that there exists some type `A` and a value of
   type `F[A]`. For instance, if you want to witness that a some type
   `T` has an instance of `Show[T]`, you can provide
   `Exists[λ[α => (α, Show[α])]]`.
 * `Forall[F[_]]` is a universal quantification encoded as a type in Scala.
   If you want to witness that some type `F[_]` has a monoid instance
   regardless of the type argument, you can provide
   `Forall[λ[α => Monoid[F[α]]]]`.

## Quick Start
```scala
resolvers += Resolver.bintrayRepo("alexknvl", "maven")
libraryDependencies += "com.alexknvl"  %%  "leibniz" % "0.9.0"
```

## License
Code is provided under the MIT license available at https://opensource.org/licenses/MIT,
as well as in the LICENSE file.
