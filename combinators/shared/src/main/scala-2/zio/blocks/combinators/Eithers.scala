package zio.blocks.combinators

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

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
 *   - `separate` is the inverse of `combine`
 *
 * @example
 *   {{{
 * import zio.blocks.combinators.Eithers._
 *
 * val combined = Eithers.combine(Right(Right(true)): Either[Int, Either[String, Boolean]])
 * // Result: Right(true): Either[Either[Int, String], Boolean]
 *   }}}
 */
object Eithers {

  trait Eithers[L, R] {
    type Out

    def combine(either: Either[L, R]): Out

    def separate(out: Out): Either[L, R]
  }

  object Eithers {
    type WithOut[L, R, O] = Eithers[L, R] { type Out = O }

    implicit def combineEither[L, R]: Eithers[L, R] = macro EithersMacros.eithersImpl[L, R]
  }

  // Backward-compatible aliases
  type Combiner[L, R] = Eithers[L, R]

  object Combiner {
    type WithOut[L, R, O] = Eithers.WithOut[L, R, O]
  }

  // Backward-compatible Separator trait
  trait Separator[A] {
    type Left
    type Right

    def separate(a: A): Either[Left, Right]
  }

  object Separator {
    type WithTypes[A, L, R] = Separator[A] { type Left = L; type Right = R }

    implicit def separator[L, R](implicit
      c: Eithers[L, R]
    ): Separator[Either[L, R]] =
      new Separator[Either[L, R]] {
        type Left  = Any
        type Right = Any

        def separate(a: Either[L, R]): Either[Any, Any] =
          c.combine(a).asInstanceOf[Either[Any, Any]]
      }
  }

  def combine[L, R](either: Either[L, R])(implicit c: Eithers[L, R]): c.Out = c.combine(either)
  def separate[A](a: A)(implicit s: Separator[A]): Either[s.Left, s.Right]  = s.separate(a)

  private[combinators] object EithersMacros {

    private def isEither(c: whitebox.Context)(tpe: c.universe.Type): Boolean = {
      val sym = tpe.typeSymbol
      sym.fullName == "scala.util.Either"
    }

    private def eitherTypes(c: whitebox.Context)(tpe: c.universe.Type): (c.universe.Type, c.universe.Type) = {
      val args = tpe.dealias.typeArgs
      (args(0), args(1))
    }

    private def collectLeaves(c: whitebox.Context)(tpe: c.universe.Type): List[c.universe.Type] =
      if (!isEither(c)(tpe)) {
        List(tpe)
      } else {
        val (left, right) = eitherTypes(c)(tpe)
        collectLeaves(c)(left) ++ collectLeaves(c)(right)
      }

    private def buildLeftNested(c: whitebox.Context)(types: List[c.universe.Type]): c.universe.Type = {
      import c.universe._
      types match {
        case Nil                     => c.abort(c.enclosingPosition, "Cannot build Either from empty list")
        case single :: Nil           => single
        case first :: second :: rest =>
          val initial = appliedType(typeOf[Either[_, _]].typeConstructor, List(first, second))
          rest.foldLeft(initial) { (acc, tpe) =>
            appliedType(typeOf[Either[_, _]].typeConstructor, List(acc, tpe))
          }
      }
    }

    def eithersImpl[L: c.WeakTypeTag, R: c.WeakTypeTag](c: whitebox.Context): c.Tree = {
      import c.universe._

      val lType        = weakTypeOf[L].dealias
      val rType        = weakTypeOf[R].dealias
      val inputEither  = appliedType(typeOf[Either[_, _]].typeConstructor, List(lType, rType))
      val leaves       = collectLeaves(c)(inputEither)
      val outType      = buildLeftNested(c)(leaves)
      val combineBody  = generateCombineBody(c)(lType, rType)
      val separateBody = generateSeparateBody(c)(lType, rType)

      q"""
        new _root_.zio.blocks.combinators.Eithers.Eithers[$lType, $rType] {
          type Out = $outType
          def combine(either: Either[$lType, $rType]): $outType = $combineBody
          def separate(out: $outType): Either[$lType, $rType] = $separateBody
        }
      """
    }

    private def generateCombineBody(c: whitebox.Context)(
      lType: c.universe.Type,
      rType: c.universe.Type
    ): c.Tree = {
      import c.universe._

      if (!isEither(c)(lType) && !isEither(c)(rType)) {
        q"either"
      } else {
        val lLeaves   = collectLeaves(c)(lType)
        val rLeaves   = collectLeaves(c)(rType)
        val allLeaves = lLeaves ++ rLeaves

        val caseDefs = allLeaves.zipWithIndex.map { case (_, idx) =>
          val isFromLeft = idx < lLeaves.length
          val localIdx   = if (isFromLeft) idx else idx - lLeaves.length

          val pattern = if (isFromLeft) {
            buildExtractionPattern(c)(lType, localIdx, lLeaves.length, isLeft = true)
          } else {
            buildExtractionPattern(c)(rType, localIdx, rLeaves.length, isLeft = false)
          }

          val result = buildLeftNestedResult(c)(idx, allLeaves.length)

          cq"$pattern => $result"
        }

        q"either match { case ..$caseDefs }"
      }
    }

    private def generateSeparateBody(c: whitebox.Context)(
      lType: c.universe.Type,
      rType: c.universe.Type
    ): c.Tree = {
      import c.universe._

      if (!isEither(c)(lType) && !isEither(c)(rType)) {
        q"out"
      } else {
        val lLeaves   = collectLeaves(c)(lType)
        val rLeaves   = collectLeaves(c)(rType)
        val allLeaves = lLeaves ++ rLeaves

        val caseDefs = allLeaves.zipWithIndex.map { case (_, idx) =>
          val pattern = buildLeftNestedPattern(c)(idx, allLeaves.length)

          val isFromLeft = idx < lLeaves.length
          val localIdx   = if (isFromLeft) idx else idx - lLeaves.length

          val result = if (isFromLeft) {
            buildRightNestedResult(c)(lType, localIdx, lLeaves.length, isLeft = true)
          } else {
            buildRightNestedResult(c)(rType, localIdx, rLeaves.length, isLeft = false)
          }

          cq"$pattern => $result"
        }

        q"out match { case ..$caseDefs }"
      }
    }

    private def buildExtractionPattern(c: whitebox.Context)(
      tpe: c.universe.Type,
      leafIdx: Int,
      totalLeaves: Int,
      isLeft: Boolean
    ): c.Tree = {
      import c.universe._

      if (totalLeaves == 1) {
        if (isLeft) pq"Left(x)" else pq"Right(x)"
      } else {
        val innerPattern = buildNestedPattern(c)(tpe, leafIdx)
        if (isLeft) pq"Left($innerPattern)" else pq"Right($innerPattern)"
      }
    }

    private def buildNestedPattern(c: whitebox.Context)(
      tpe: c.universe.Type,
      leafIdx: Int
    ): c.Tree = {
      import c.universe._

      if (!isEither(c)(tpe)) {
        pq"x"
      } else {
        val (leftType, rightType) = eitherTypes(c)(tpe)
        val leftLeaves            = collectLeaves(c)(leftType)

        if (leafIdx < leftLeaves.length) {
          val inner = buildNestedPattern(c)(leftType, leafIdx)
          pq"Left($inner)"
        } else {
          val inner = buildNestedPattern(c)(rightType, leafIdx - leftLeaves.length)
          pq"Right($inner)"
        }
      }
    }

    private def buildLeftNestedResult(c: whitebox.Context)(
      leafIdx: Int,
      totalLeaves: Int
    ): c.Tree = {
      import c.universe._

      if (totalLeaves == 1) {
        q"x"
      } else if (leafIdx == totalLeaves - 1) {
        q"Right(x)"
      } else {
        buildLeftNestedWrapper(c)(leafIdx, totalLeaves)
      }
    }

    private def buildLeftNestedWrapper(c: whitebox.Context)(
      leafIdx: Int,
      totalLeaves: Int
    ): c.Tree = {
      import c.universe._

      def wrap(idx: Int, depth: Int): c.Tree =
        if (depth == 1) {
          if (idx == 0) q"Left(x)" else q"Right(x)"
        } else {
          if (idx == depth) {
            q"Right(x)"
          } else {
            val inner = wrap(idx, depth - 1)
            q"Left($inner)"
          }
        }

      wrap(leafIdx, totalLeaves - 1)
    }

    private def buildLeftNestedPattern(c: whitebox.Context)(
      leafIdx: Int,
      totalLeaves: Int
    ): c.Tree = {
      import c.universe._

      if (totalLeaves == 1) {
        pq"x"
      } else if (leafIdx == totalLeaves - 1) {
        pq"Right(x)"
      } else {
        buildLeftNestedPatternWrapper(c)(leafIdx, totalLeaves)
      }
    }

    private def buildLeftNestedPatternWrapper(c: whitebox.Context)(
      leafIdx: Int,
      totalLeaves: Int
    ): c.Tree = {
      import c.universe._

      def wrap(idx: Int, depth: Int): c.Tree =
        if (depth == 1) {
          if (idx == 0) pq"Left(x)" else pq"Right(x)"
        } else {
          if (idx == depth) {
            pq"Right(x)"
          } else {
            val inner = wrap(idx, depth - 1)
            pq"Left($inner)"
          }
        }

      wrap(leafIdx, totalLeaves - 1)
    }

    private def buildRightNestedResult(c: whitebox.Context)(
      tpe: c.universe.Type,
      leafIdx: Int,
      totalLeaves: Int,
      isLeft: Boolean
    ): c.Tree = {
      import c.universe._

      if (totalLeaves == 1) {
        if (isLeft) q"Left(x)" else q"Right(x)"
      } else {
        val innerResult = buildNestedResult(c)(tpe, leafIdx)
        if (isLeft) q"Left($innerResult)" else q"Right($innerResult)"
      }
    }

    private def buildNestedResult(c: whitebox.Context)(
      tpe: c.universe.Type,
      leafIdx: Int
    ): c.Tree = {
      import c.universe._

      if (!isEither(c)(tpe)) {
        q"x"
      } else {
        val (leftType, rightType) = eitherTypes(c)(tpe)
        val leftLeaves            = collectLeaves(c)(leftType)

        if (leafIdx < leftLeaves.length) {
          val inner = buildNestedResult(c)(leftType, leafIdx)
          q"Left($inner)"
        } else {
          val inner = buildNestedResult(c)(rightType, leafIdx - leftLeaves.length)
          q"Right($inner)"
        }
      }
    }
  }
}
