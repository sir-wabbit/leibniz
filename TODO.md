# Inference

### Inhabitance

```scala

import leibniz._

import leibniz.inhabitance._

type +[A, B] = Either[A, B]
type *[A, B] = (A, B)
type Fix[F[_]]
type ∃[+A] = Inhabited[A]
type !∃[-A] = Uninhabited[A]

implicit val v: !∃[Void] = ???
implicit val u: ∃[Unit] = ???

implicit def fix[F[_]](implicit f: ∃[F[Void]]): ∃[Fix[F]] = ???

implicit def inhSumL[A, B](implicit f: ∃[A]): ∃[A + B] = ???
implicit def inhSumR[A, B](implicit f: ∃[B]): ∃[A + B] = ???
implicit def uninhSumL[A, B](implicit A: !∃[A], B: !∃[B]): !∃[A + B] = ???

implicit def uninhProductL[A, B](implicit f: !∃[A]): !∃[A * B] = ???
implicit def uninhProductR[A, B](implicit f: !∃[B]): !∃[A * B] = ???
implicit def inhProduct[A, B](implicit A: ∃[A], B: ∃[B]): ∃[A * B] = ???
```

Inhabited[F[Void]]
Uninhabited[F[Void]]