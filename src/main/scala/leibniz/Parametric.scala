package leibniz

import leibniz.inhabitance.Inhabited

/**
  * a ≠ b ⋀ f a = f b ⟶ ∀ x y. x ≠ y ⟶ f x = f y
  * a < b ⋀ f a ≤ f b ⟶ ∀ x y. x < y ⟶ f x ≤ f y
  * a < b ⋀ f a ≥ f b ⟶ ∀ x y. x < y ⟶ f x ≥ f y
  * a < b ⋀ f a ≸ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y
  */
trait Parametric[F[_]] {

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // a ≠ b ⋀ f a = f b ⟶ ∀ x y. x ≠ y ⟶ f x = f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a ≠ b ⋀ f a = f b ⟶ ∀ x y. x ≠ y ⟶ f x = f y
    */
  def liftPh[A, B, X, Y](ab: A =!= B, fab: F[A] === F[B]): F[X] === F[Y]

  /**
    * a ≠ b ⋀ f a = f b ⟶ ∀ x y. f x ≠ f y ⟶ x = y
    * `f x ≠ f y` implies `x ≠ y`, therefore it is a contradiction.
    */
  def lowerPh[A, B, X, Y](nab: A =!= B, fab: F[A] === F[B], nfxy: F[X] =!= F[Y]): Void =
    nfxy(liftPh(nab, fab))

  /**
    * a ≠ b ⋀ f a ≠ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≠ f y
    * `f a ≠ f b` implies `a ≠ b`.
    */
  def liftInj[A, B, X, Y](nfab: F[A] =!= F[B], nxy: X =!= Y): F[X] =!= F[Y] =
    WeakApart { fxy => nfab(liftPh(nxy, fxy)) }

  /**
    * a ≠ b ⋀ f a ≠ f b ⟶ ∀ x y. f x = f y ⟶ x = y
    */
  def lowerInj[A, B, X, Y](nfab: F[A] =!= F[B], fxy: F[X] === F[Y]): X === Y =
    Inhabited.witness[X === Y] { nxy => nfab(liftPh(WeakApart(nxy), fxy)) }.proved

  /////////////////////////////////////////////////////////////////////////////////////////////////
  //   a < b  ⋀   f a ≤ f b ⟶ ∀ x y. x < y ⟶ f x ≤ f y
  // ¬(a < b) ⋁ ¬(f a ≤ f b) ⋁   ¬(x < y)    ⋁ f x ≤ f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a < b ⋀ f a ≤ f b ⟶ ∀ x y. x < y ⟶ f x ≤ f y
    */
  def liftCv[A, B, X, Y](ab: A </< B, fab: F[A] <~< F[B], xy: X </< Y): F[X] <~< F[Y]

  /**
    * a < b ⋀ f a ≤ f b ⟶ ∀ x y. ¬(f x ≤ f y) ⟶ ¬(x < y)
    */
  def lowerCv[A, B, X, Y](ab: A </< B, fab: F[A] <~< F[B], nfxy: ¬[F[X] <~< F[Y]]): ¬[X </< Y] =
    xy => nfxy(liftCv(ab, fab, xy))

  /**
    * a < b ⋀ ¬(f a ≤ f b) ⟶ ∀ x y. x < y ⟶ ¬(f x ≤ f y)
    */
  def liftNonCv[A, B, X, Y](ab: A </< B, nfab: ¬[F[A] <~< F[B]], xy: X </< Y): ¬[F[X] <~< F[Y]] =
    nfxy => nfab(liftCv[X, Y, A, B](xy, nfxy, ab))

  /**
    * a < b ⋀ ¬(f a ≤ f b) ⟶ ∀ x y. f x ≤ f y ⟶ ¬[x < y]
    */
  def lowerNonCv[A, B, X, Y](ab: A </< B, nfab: ¬[F[A] <~< F[B]], fxy: F[X] <~< F[Y]): ¬[X </< Y] =
    xy => nfab(liftCv[X, Y, A, B](xy, fxy, ab))

  /////////////////////////////////////////////////////////////////////////////////////////////////
  //   a < b ⋀ f a ≥ f b ⟶ ∀ x y. x < y ⟶ f x ≥ f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a < b ⋀ f a ≥ f b ⟶ ∀ x y. x < y ⟶ f x ≥ f y
    */
  def liftCt[A, B, X, Y](ab:  A </< B, fba: F[B] <~< F[A], xy: X </< Y): F[Y] <~< F[X]

  /**
    * a < b ⋀ f a ≥ f b ⟶ ∀ x y. ¬(f x ≥ f y) ⟶ ¬(x < y)
    */
  def lowerCt[A, B, X, Y](ab: A </< B, fab: F[B] <~< F[A], nfxy: ¬[F[Y] <~< F[X]]): ¬[X </< Y] =
    xy => nfxy(liftCt(ab, fab, xy))

  /**
    * a < b ⋀ ¬(f a ≥ f b) ⟶ ∀ x y. x < y ⟶ ¬(f x ≥ f y)
    */
  def liftNonCt[A, B, X, Y](ab: A </< B, nfab: ¬[F[B] <~< F[A]], xy: X </< Y): ¬[F[Y] <~< F[X]] =
    nfxy => nfab(liftCt[X, Y, A, B](xy, nfxy, ab))

  /**
    * a < b ⋀ ¬(f a ≥ f b) ⟶ ∀ x y. f x ≥ f y ⟶ ¬[x < y]
    */
  def lowerNonCt[A, B, X, Y](ab: A </< B, nfab: ¬[F[B] <~< F[A]], fxy: F[Y] <~< F[X]): ¬[X </< Y] =
    xy => nfab(liftCt[X, Y, A, B](xy, fxy, ab))

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // a < b ⋀ f a ≸ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a < b ⋀ f a ≸ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y
    */
  def liftInv[A, B, X, Y](ab:  A </< B, fab: F[A] >~< F[B], xy: X =!= Y): F[X] >~< F[Y]

  /**
    * a < b ⋀ f a ≸ f b ⟶ ∀ x y. ¬(f x ≸ f y) ⟶ x = y
    */
  def lowerInv[A, B, X, Y](ab: A </< B, fab: F[A] >~< F[B], nfxy: ¬[F[X] >~< F[Y]]): X === Y =
    Is.consistent[X, Y](nxy => nfxy(liftInv(ab, fab, nxy)))

  /**
    * a ≠ b ⋀ ¬(f a ≸ f b) ⟶ ∀ x y. x < y ⟶ ¬(f x ≸ f y)
    */
  def liftNonInv[A, B, X, Y](nab: A =!= B, nfab: ¬[F[A] >~< F[B]], xy: X </< Y): ¬[F[X] >~< F[Y]] =
    nfxy => nfab(liftInv[X, Y, A, B](xy, nfxy, nab))

  /**
    * a ≠ b ⋀ ¬(f a ≸ f b) ⟶ ∀ x y. f x ≸ f y ⟶ ¬[x < y]
    */
  def lowerNonInv[A, B, X, Y](nab: A =!= B, nfab: ¬[F[A] >~< F[B]], fxy: F[X] >~< F[Y]): ¬[X </< Y] =
    xy => nfab(liftInv[X, Y, A, B](xy, fxy, nab))

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // a < b ⋀ f a < f b ⟶ ∀ x y. x < y ⟶ f x < f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a < b ⋀ f a < f b ⟶ ∀ x y. x < y ⟶ f x < f y
    */
  def liftStCv[A, B, X, Y](ab: A </< B, q: F[A] </< F[B], r: X </< Y): F[X] </< F[Y] = {
    val s: F[X] <~< F[Y] = liftCv[A, B, X, Y](ab, q.conformity, r)
    val u: F[X] =!= F[Y] = WeakApart.witness[F[X], F[Y]] { xy =>
      val v: F[A] === F[B] = liftPh[X, Y, A, B](r.inequality, xy)
      q.inequality.run(v)
    }
    StrictAs.witness(u, s)
  }

  /**
    * a < b ⋀ f a < f b ⟶ ∀ x y. ¬(f x < f y) ⟶ ¬(x < y)
    */
  def lowerStCv[A, B, X, Y](ab: A </< B, fab: F[A] </< F[B], nfxy: ¬[F[X] </< F[Y]]): ¬[X </< Y] =
    xy => nfxy(liftStCv(ab, fab, xy))

  /**
    * a < b ⋀ ¬(f a < f b) ⟶ ∀ x y. x < y ⟶ ¬(f x < f y)
    */
  def liftNonStCv[A, B, X, Y](ab: A </< B, nfab: ¬[F[A] </< F[B]], xy: X </< Y): ¬[F[X] </< F[Y]] =
    nfxy => nfab(liftStCv[X, Y, A, B](xy, nfxy, ab))

  /**
    * a < b ⋀ ¬(f a < f b) ⟶ ∀ x y. f x < f y ⟶ ¬[x < y]
    */
  def lowerNonStCv[A, B, X, Y](ab: A </< B, nfab: ¬[F[A] </< F[B]], fxy: F[X] </< F[Y]): ¬[X </< Y] =
    xy => nfab(liftStCv[X, Y, A, B](xy, fxy, ab))

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // a < b ⋀ f a > f b ⟶ ∀ x y. x < y ⟶ f x > f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a < b ⋀ f a > f b ⟶ ∀ x y. x < y ⟶ f x > f y
    */
  def liftStCt[A, B, X, Y](ab:  A </< B, q: F[B] </< F[A], r: X </< Y): F[Y] </< F[X] = {
    val s: F[Y] <~< F[X] = liftCt[A, B, X, Y](ab, q.conformity, r)
    val u: F[X] =!= F[Y] = WeakApart.witness[F[X], F[Y]] { xy =>
      val v: F[A] === F[B] = liftPh[X, Y, A, B](r.inequality, xy)
      q.inequality[F[B], F[A]].flip.run(v)
    }
    StrictAs.witness(u.flip, s)
  }

  /**
    * a < b ⋀ f a > f b ⟶ ∀ x y. ¬(f x > f y) ⟶ ¬(x < y)
    */
  def lowerStCt[A, B, X, Y](ab: A </< B, fab: F[B] </< F[A], nfxy: ¬[F[Y] </< F[X]]): ¬[X </< Y] =
    xy => nfxy(liftStCt(ab, fab, xy))

  /**
    * a < b ⋀ ¬(f a > f b) ⟶ ∀ x y. x < y ⟶ ¬(f x > f y)
    */
  def liftNonStCt[A, B, X, Y](ab: A </< B, nfab: ¬[F[B] </< F[A]], xy: X </< Y): ¬[F[Y] </< F[X]] =
    nfxy => nfab(liftStCt[X, Y, A, B](xy, nfxy, ab))

  /**
    * a < b ⋀ ¬(f a > f b) ⟶ ∀ x y. f x > f y ⟶ ¬[x < y]
    */
  def lowerNonStCt[A, B, X, Y](ab: A </< B, nfab: ¬[F[B] </< F[A]], fxy: F[Y] </< F[X]): ¬[X </< Y] =
    xy => nfab(liftStCt[X, Y, A, B](xy, fxy, ab))

  /////////////////////////////////////////////////////////////////////////////////////////////////
  // a ≸ b ⋀ f a ≠ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y
  /////////////////////////////////////////////////////////////////////////////////////////////////

  /**
    * a ≸ b ⋀ f a ≠ f b ⟶ ∀ x y. x ≠ y ⟶ f x ≸ f y
    */
  def liftInc[A, B, X, Y](ab: A >~< B, nfxy: F[A] =!= F[B], nxy: X =!= Y): F[X] >~< F[Y] =
    Axioms.parametricity1[F, A, B, X, Y](ab, nfxy, nxy)

  /**
    * a ≸ b ⋀ f a ≠ f b ⟶ ∀ x y. ¬(f x ≸ f y) ⟶ x = y
    */
  def lowerInc[A, B, X, Y](ab: A >~< B, nfab: F[A] =!= F[B], nfxy: ¬[F[X] >~< F[Y]]): X === Y =
    Is.consistent[X, Y](nxy => nfxy(liftInc[A, B, X, Y](ab, nfab, nxy)))


  /**
    * a ≠ b ⋀ ¬(f a ≸ f b) ⟶ ∀ x y. x ≸ y ⟶ f x = f y
    */
  def idkHowToNameThese1[A, B, X, Y](nab: A =!= B, nfab: ¬[F[A] >~< F[B]], xy: X >~< Y): F[X] === F[Y] =
    Is.consistent[F[X], F[Y]](nfxy => nfab(liftInc[X, Y, A, B](xy, nfxy, nab)))

  /**
    * a ≠ b ⋀ ¬(f a ≸ f b) ⟶ ∀ x y. f x ≠ f y ⟶ ¬(x ≸ y)
    */
  def idkHowToNameThese2[A, B, X, Y](nab: A =!= B, nfab: ¬[F[A] >~< F[B]], nfxy: F[X] =!= F[Y]): ¬[X >~< Y] =
    nxy => nfab(liftInc[X, Y, A, B](nxy, nfxy, nab))
}
object Parametric {
  def apply[F[_]](implicit F: Parametric[F]): Parametric[F] = F

  /**
    * Every type constructor is parametric.
    */
  implicit def instance[F[_]]: Parametric[F] = new Parametric[F] {
    def liftPh[A, B, X, Y](ab: A =!= B, fab: F[A] === F[B]): F[X] === F[Y] =
      Axioms.phParametricity[F, A, B, X, Y](fab, ab.run)

    def liftCv[A, B, X, Y](ab: A </< B, q: F[A] <~< F[B], r: X </< Y): F[X] <~< F[Y] =
      Axioms.cvParametricity[F, A, B, X, Y](ab.inequality.run, ab.conformity, q, r.conformity)

    def liftCt[A, B, X, Y](ab:  A </< B, q: F[B] <~< F[A], r: X </< Y): F[Y] <~< F[X] =
      Axioms.ctParametricity[F, A, B, X, Y](ab.inequality.run, ab.conformity, q, r.conformity)

    def liftInv[A, B, X, Y](ab:  A </< B, fab: F[A] >~< F[B], nxy: X =!= Y): F[X] >~< F[Y] =
      Axioms.invParametricity[F, A, B, X, Y](ab, fab, nxy)
  }
}