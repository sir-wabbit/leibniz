# Leibniz

Leibniz equivalence and Liskov substitutability library for Scala.

## Leibniz
The Leibnitz’ equality law states that if `a` and `b` are identical then they
must have identical properties. Leibnitz’ original definition reads as follows:
```
a ≡ b = ∀ f .f a ⇔ f b
```
and can be proven to be equivalent to:
```
a ≡ b = ∀ f .f a → f b
```

In Scala we can encode this law as:
```scala
trait Leibniz[A, B] {
  def subst[F[_]](fa: F[A]): F[B]
}
```

The `Leibniz` data type then encodes true type equality, since the identity
function is the only non-diverging conversion function that can be used
as an implementation of the `subst` method assuming that we do not break
parametricity. As the substitution function has to work for any `F[_]`, it
cannot make assumptions about the structure of `F[_]`, making it impossible
to construct a value of type `F[A]` or to access values of type `A` that
may be stored inside a value of type `F[A]`. Hence it is impossible for
a substitution function to alter the value it takes as argument.

Not taking into account the partial functions that never terminate
(infinite loops), functions returning `null`, or throwing exceptions,
the identity function is the only function that can be used in place of
`subst` to construct a value of type `Leibniz[A, B]`.

The existence of a value of type `Leibniz[A, B]` now implies that a ≡ b,
since the conversion function, that converts an `A` into a `B`, must be
the identity function.

This technique was first used in [Typing Dynamic Typing](http://portal.acm.org/citation.cfm?id=583852.581494) (Baars and Swierstra, ICFP 2002).

You can find some further examples [here](http://typelevel.org/blog/2014/09/20/higher_leibniz.html).


## Liskov

`Liskov[A, B]` witnesses that `A` can be used in any negative context
that expects a `B`. (e.g. if you could pass an `A` into any function
that expects a `B`.)

TODO: Expand on this.

## Quick Start
```scala
resolvers += Resolver.bintrayRepo("alexknvl", "maven")
libraryDependencies += "com.alexknvl"  %%  "leibniz" % "0.1"
```

## License
Code is provided under the MIT license available at https://opensource.org/licenses/MIT,
as well as in the LICENSE file.