package zio.blocks.combinators

import scala.compiletime.erasedValue

/**
 * Either operations: combining values into left-nested canonical form and
 * separating them.
 *
 * The `Eithers` module provides a unified typeclass `Eithers[L, R]` that both
 * combines an `Either[L, R]` into left-nested canonical form and separates it
 * back.
 *
 * Key behaviors:
 *   - Canonical form is left-nested: `Either[Either[Either[A, B], C], D]`
 *   - `combine` takes `Either[L, R]` as input and produces the canonical form
 *   - `separate` is the inverse: takes the canonical form and reconstructs the
 *     original `Either[L, R]`
 *
 * @example
 *   {{{
 * import zio.blocks.combinators.Eithers._
 *
 * // Combine reassociates to left-nested form
 * val combined = Eithers.combine(Right(Right(true)): Either[Int, Either[String, Boolean]])
 * // Result: Right(true): Either[Either[Int, String], Boolean]
 *
 * // Separate peels the rightmost alternative
 * val separated = Eithers.separate(Right(true): Either[Either[Int, String], Boolean])
 * // Result: Right(true): Either[Either[Int, String], Boolean]
 *   }}}
 */
object Eithers {

  /**
   * Computes the left-nested canonical form for Either[L, R].
   *
   * Recursively reassociates right-nested Eithers to left-nested form:
   *   - `Either[L, Either[X, Y]]` becomes `LeftNest[Either[L, X], Y]`
   *   - Atomic right types remain as `Either[L, R]`
   */
  type LeftNest[L, R] <: Either[?, ?] = R match {
    case Either[x, y] => LeftNest[Either[L, x], y]
    case _            => Either[L, R]
  }

  /**
   * Canonicalizes a type, recursively canonicalizing nested Eithers.
   */
  type Canonicalize[E] = E match {
    case Either[l, r] => CanonicalizeEither[l, r]
    case _            => E
  }

  /**
   * Canonicalizes an Either by first canonicalizing both branches, then
   * reassociating to left-nested form.
   */
  type CanonicalizeEither[L, R] <: Either[?, ?] = R match {
    case Either[x, y] => CanonicalizeEither[Either[Canonicalize[L], Canonicalize[x]], y]
    case _            => Either[Canonicalize[L], Canonicalize[R]]
  }

  /**
   * Extracts the left type from a left-nested Either.
   */
  type LeftOf[A] = A match {
    case Either[l, r] => l
  }

  /**
   * Extracts the right type from a left-nested Either.
   */
  type RightOf[A] = A match {
    case Either[l, r] => r
  }

  /**
   * Unified trait that combines an Either[L, R] into left-nested canonical form
   * and separates it back.
   *
   * @tparam L
   *   The left input type
   * @tparam R
   *   The right input type
   */
  trait Eithers[L, R] {
    type Out

    /**
     * Combines an Either[L, R] into left-nested canonical form.
     *
     * @param either
     *   The Either value to canonicalize
     * @return
     *   The left-nested canonical form
     */
    def combine(either: Either[L, R]): Out

    /**
     * Separates a canonical form back into the original Either[L, R].
     *
     * This is the inverse of `combine`:
     * `separate(combine(e)) == e` for all `e: Either[L, R]`
     *
     * @param out
     *   The canonical form
     * @return
     *   The original Either[L, R]
     */
    def separate(out: Out): Either[L, R]
  }

  object Eithers {
    type WithOut[L, R, O] = Eithers[L, R] { type Out = O }

    inline given eithers[L, R]: WithOut[L, R, CanonicalizeEither[L, R]] =
      inline erasedValue[L] match {
        case _: Either[a, b] =>
          inline erasedValue[R] match {
            case _: Either[x, y] =>
              LeftNestedNestedInstance[a, b, x, y]().asInstanceOf[WithOut[L, R, CanonicalizeEither[L, R]]]
            case _ =>
              LeftNestedInstance[a, b, R]().asInstanceOf[WithOut[L, R, CanonicalizeEither[L, R]]]
          }
        case _ =>
          inline erasedValue[R] match {
            case _: Either[x, y] =>
              NestedInstance[L, x, y]().asInstanceOf[WithOut[L, R, CanonicalizeEither[L, R]]]
            case _ =>
              AtomicInstance[L, R]().asInstanceOf[WithOut[L, R, CanonicalizeEither[L, R]]]
          }
      }

    private[combinators] class AtomicInstance[L, R] extends Eithers[L, R] {
      type Out = Either[L, R]

      def combine(either: Either[L, R]): Either[L, R] = either

      def separate(out: Either[L, R]): Either[L, R] = out
    }

    private[combinators] class NestedInstance[L, X, Y](using
      inner: Eithers.WithOut[Either[L, X], Y, CanonicalizeEither[Either[L, X], Y]]
    ) extends Eithers[L, Either[X, Y]] {
      type Out = CanonicalizeEither[Either[L, X], Y]

      def combine(either: Either[L, Either[X, Y]]): CanonicalizeEither[Either[L, X], Y] =
        either match {
          case Left(l)         => inner.combine(Left(Left(l)))
          case Right(Left(x))  => inner.combine(Left(Right(x)))
          case Right(Right(y)) => inner.combine(Right(y))
        }

      def separate(out: CanonicalizeEither[Either[L, X], Y]): Either[L, Either[X, Y]] =
        inner.separate(out) match {
          case Left(Left(l))  => Left(l)
          case Left(Right(x)) => Right(Left(x))
          case Right(y)       => Right(Right(y))
        }
    }

    private[combinators] class LeftNestedInstance[A, B, R](using
      val leftEithers: Eithers[A, B]
    ) extends Eithers[Either[A, B], R] {
      type Out = Either[leftEithers.Out, R]

      def combine(either: Either[Either[A, B], R]): Either[leftEithers.Out, R] =
        either match {
          case Left(ab) => Left(leftEithers.combine(ab))
          case Right(r) => Right(r)
        }

      def separate(out: Either[leftEithers.Out, R]): Either[Either[A, B], R] =
        out match {
          case Left(ab) => Left(leftEithers.separate(ab))
          case Right(r) => Right(r)
        }
    }

    private[combinators] class LeftNestedNestedInstance[A, B, X, Y](using
      val leftEithers: Eithers[A, B],
      val inner: Eithers.WithOut[Either[leftEithers.Out, X], Y, CanonicalizeEither[Either[leftEithers.Out, X], Y]]
    ) extends Eithers[Either[A, B], Either[X, Y]] {
      type Out = CanonicalizeEither[Either[leftEithers.Out, X], Y]

      def combine(
        either: Either[Either[A, B], Either[X, Y]]
      ): CanonicalizeEither[Either[leftEithers.Out, X], Y] =
        either match {
          case Left(l)         => inner.combine(Left(Left(leftEithers.combine(l))))
          case Right(Left(x))  => inner.combine(Left(Right(x)))
          case Right(Right(y)) => inner.combine(Right(y))
        }

      def separate(out: CanonicalizeEither[Either[leftEithers.Out, X], Y]): Either[Either[A, B], Either[X, Y]] =
        inner.separate(out) match {
          case Left(Left(l))  => Left(leftEithers.separate(l))
          case Left(Right(x)) => Right(Left(x))
          case Right(y)       => Right(Right(y))
        }
    }
  }

  // Backward-compatible aliases for Combiner
  type Combiner[L, R] = Eithers[L, R]

  object Combiner {
    type WithOut[L, R, O] = Eithers.WithOut[L, R, O]
  }

  // Backward-compatible Separator trait (keyed on the combined type A)
  trait Separator[A] {
    type Left
    type Right

    /**
     * Separates a combined value by peeling the rightmost alternative.
     *
     * @param a
     *   The combined value
     * @return
     *   Either[Left, Right] where Right is the rightmost alternative
     */
    def separate(a: A): Either[Left, Right]
  }

  object Separator {

    /**
     * Type alias for a Separator with specific left and right types.
     */
    type WithTypes[A, L, R] = Separator[A] { type Left = L; type Right = R }

    inline given separator[L, R](using
      c: Eithers.WithOut[L, R, CanonicalizeEither[L, R]]
    ): WithTypes[Either[L, R], LeftOf[CanonicalizeEither[L, R]], RightOf[CanonicalizeEither[L, R]]] =
      new CanonicalSeparator[L, R]

    private[combinators] class CanonicalSeparator[L, R](using
      c: Eithers.WithOut[L, R, CanonicalizeEither[L, R]]
    ) extends Separator[Either[L, R]] {
      type Left  = LeftOf[CanonicalizeEither[L, R]]
      type Right = RightOf[CanonicalizeEither[L, R]]

      def separate(a: Either[L, R]): Either[Left, Right] =
        c.combine(a).asInstanceOf[Either[Left, Right]]
    }
  }

  def combine[L, R](either: Either[L, R])(using e: Eithers[L, R]): e.Out = e.combine(either)
  def separate[A](a: A)(using s: Separator[A]): Either[s.Left, s.Right]   = s.separate(a)
}
