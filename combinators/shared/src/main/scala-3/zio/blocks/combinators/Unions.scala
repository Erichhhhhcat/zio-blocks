package zio.blocks.combinators

import scala.quoted.*
import scala.reflect.TypeTest

/**
 * Union operations: combining values into flat union types and separating them.
 *
 * The `Unions` module provides a unified typeclass `Unions[L, R]` that both
 * combines an `Either[L, R]` into a union type `L | R` and separates it back.
 *
 * Key behaviors:
 *   - Canonical form is flat union: `A | B | C | D`
 *   - `combine` takes `Either[L, R]` as input and produces union `L | R`
 *   - `separate` uses TypeTest to discriminate the rightmost type, bridging the
 *     untagged world to the tagged world
 *
 * Caveat: Union discrimination is fragile for erased types (e.g.,
 * `List[Int] | List[String]`). Works reliably for distinct concrete types.
 *
 * @example
 *   {{{
 * import zio.blocks.combinators.Unions._
 *
 * // Combine Either to union
 * val combined: Int | String = Unions.combine(Left(42): Either[Int, String])
 * // Result: 42: Int | String
 *
 * // Separate discriminates rightmost type
 * val separated = Unions.separate(true: Int | String | Boolean)
 * // Result: Right(true): Either[Int | String, Boolean]
 *   }}}
 */
object Unions {

  /**
   * Unified trait that combines an Either[L, R] into a union type L | R and
   * separates it back.
   *
   * @tparam L
   *   The left input type
   * @tparam R
   *   The right input type
   */
  trait Unions[L, R] {
    type Out

    /**
     * Combines an Either[L, R] into a union type.
     *
     * @param either
     *   The Either value to convert to union
     * @return
     *   The union type L | R
     */
    def combine(either: Either[L, R]): Out

    /**
     * Separates a union value back into Either[L, R].
     *
     * This is the inverse of `combine`: `separate(combine(e)) == e` for all
     * `e: Either[L, R]`
     *
     * @param out
     *   The union value
     * @return
     *   Either[L, R] discriminated by TypeTest
     */
    def separate(out: Out): Either[L, R]
  }

  object Unions {
    type WithOut[L, R, O] = Unions[L, R] { type Out = O }

    inline given unions[L, R](using tt: TypeTest[L | R, R]): WithOut[L, R, L | R] =
      ${ unionsMacro[L, R]('tt) }

    private def unionsMacro[L: Type, R: Type](
      tt: Expr[TypeTest[L | R, R]]
    )(using Quotes): Expr[WithOut[L, R, L | R]] = {
      import quotes.reflect.*

      def flattenUnion(tpe: TypeRepr): List[TypeRepr] = tpe.dealias match {
        case OrType(left, right) => flattenUnion(left) ++ flattenUnion(right)
        case other               => List(other)
      }

      val lTypes = flattenUnion(TypeRepr.of[L])
      val rTypes = flattenUnion(TypeRepr.of[R])

      val overlap = lTypes.filter { lType =>
        rTypes.exists(rType => lType =:= rType)
      }

      if (overlap.nonEmpty) {
        val overlapNames = overlap.map(_.typeSymbol.name).mkString(", ")
        report.errorAndAbort(
          s"Union types must contain unique types. Found overlapping types: $overlapNames. " +
            "Use Either, a wrapper type, opaque type, or newtype to distinguish values of the same underlying type."
        )
      }

      '{ new UnionInstance[L, R](using $tt) }
    }

    private[combinators] class UnionInstance[L, R](using tt: TypeTest[L | R, R]) extends Unions[L, R] {
      type Out = L | R

      def combine(either: Either[L, R]): L | R = either match {
        case Left(l)  => l
        case Right(r) => r
      }

      def separate(out: L | R): Either[L, R] = out match {
        case tt(r) => Right(r)
        case _     => Left(out.asInstanceOf[L])
      }
    }
  }

  // Backward-compatible aliases for Combiner
  type Combiner[L, R] = Unions[L, R]

  object Combiner {
    type WithOut[L, R, O] = Unions.WithOut[L, R, O]
  }

  // Backward-compatible Separator trait (keyed on the union type A)
  trait Separator[A] {
    type Left
    type Right

    /**
     * Separates a union value by discriminating the rightmost type.
     *
     * @param a
     *   The union value
     * @return
     *   Either[Left, Right] where Right is the rightmost type in the union
     */
    def separate(a: A): Either[Left, Right]
  }

  object Separator {
    type WithTypes[A, L, R] = Separator[A] { type Left = L; type Right = R }

    inline given separator[L, R](using tt: TypeTest[L | R, R]): WithTypes[L | R, L, R] =
      ${ separatorMacro[L, R]('tt) }

    private def separatorMacro[L: Type, R: Type](
      tt: Expr[TypeTest[L | R, R]]
    )(using Quotes): Expr[WithTypes[L | R, L, R]] = {
      import quotes.reflect.*

      def flattenUnion(tpe: TypeRepr): List[TypeRepr] = tpe.dealias match {
        case OrType(left, right) => flattenUnion(left) ++ flattenUnion(right)
        case other               => List(other)
      }

      val lTypes = flattenUnion(TypeRepr.of[L])
      val rTypes = flattenUnion(TypeRepr.of[R])

      val overlap = lTypes.filter { lType =>
        rTypes.exists(rType => lType =:= rType)
      }

      if (overlap.nonEmpty) {
        val overlapNames = overlap.map(_.typeSymbol.name).mkString(", ")
        report.errorAndAbort(
          s"Union types must contain unique types. Found overlapping types: $overlapNames. " +
            "Use Either, a wrapper type, opaque type, or newtype to distinguish values of the same underlying type."
        )
      }

      '{ new UnionSeparator[L, R](using $tt) }
    }

    private[combinators] class UnionSeparator[L, R](using tt: TypeTest[L | R, R]) extends Separator[L | R] {
      type Left  = L
      type Right = R

      def separate(a: L | R): Either[L, R] = a match {
        case tt(r) => Right(r)
        case _     => Left(a.asInstanceOf[L])
      }
    }
  }

  def combine[L, R](either: Either[L, R])(using u: Unions[L, R]): u.Out = u.combine(either)
  def separate[A](a: A)(using s: Separator[A]): Either[s.Left, s.Right] = s.separate(a)
}
