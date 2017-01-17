package object leibniz {
  type ===[A, B] = Leibniz[A, B]

  type <~<[-A, +B] = Liskov[A, B]
  type >~>[+A, -B] = Liskov[B, A]
}
