package zio.blocks.combinators

import scala.language.experimental.macros
import scala.reflect.macros.whitebox

/**
 * Tuple operations: combining values into flat tuples and separating them.
 *
 * The `Tuples` module provides a unified typeclass `Tuples[L, R]` that both
 * combines two values into a flattened output and separates them back.
 *
 * Key behaviors:
 *   - Unit identity: `combine((), a)` returns `a`
 *   - Tuple flattening: `combine((a, b), c)` returns `(a, b, c)`
 *   - `separate` is the inverse of `combine`
 *
 * Scala 2 limitation: Maximum tuple arity is 22.
 *
 * @example
 *   {{{
 * import zio.blocks.combinators.Tuples._
 *
 * val combined: (Int, String, Boolean) = Tuples.combine((1, "a"), true)
 * val (left, right) = Tuples.separate(combined)
 *   }}}
 */
object Tuples {

  trait Tuples[L, R] {
    type Out

    def combine(l: L, r: R): Out

    def separate(out: Out): (L, R)
  }

  object Tuples extends TuplesLowPriority1 {
    type WithOut[L, R, O] = Tuples[L, R] { type Out = O }

    implicit def leftUnit[A]: WithOut[Unit, A, A] =
      new Tuples[Unit, A] {
        type Out = A
        def combine(l: Unit, r: A): A   = r
        def separate(out: A): (Unit, A) = ((), out)
      }

    implicit def rightUnit[A]: WithOut[A, Unit, A] =
      new Tuples[A, Unit] {
        type Out = A
        def combine(l: A, r: Unit): A   = l
        def separate(out: A): (A, Unit) = (out, ())
      }
  }

  trait TuplesLowPriority1 {
    implicit def combineTuple[L, R]: Tuples[L, R] = macro TuplesMacros.tuplesImpl[L, R]
  }

  // Backward-compatible aliases
  type Combiner[L, R] = Tuples[L, R]

  object Combiner {
    type WithOut[L, R, O] = Tuples.WithOut[L, R, O]
  }

  // Backward-compatible Separator trait
  trait Separator[A] {
    type Left
    type Right

    def separate(a: A): (Left, Right)
  }

  object Separator extends SeparatorLowPriority1 {
    type WithTypes[A, L, R] = Separator[A] { type Left = L; type Right = R }

    implicit def separateTuple[A]: Separator[A] = macro TuplesMacros.separatorImpl[A]
  }

  trait SeparatorLowPriority1 extends SeparatorLowPriority2 {
    implicit def leftUnitSep[A]: Separator.WithTypes[A, Unit, A] =
      new Separator[A] {
        type Left  = Unit
        type Right = A
        def separate(a: A): (Unit, A) = ((), a)
      }

    implicit def rightUnitSep[A]: Separator.WithTypes[A, A, Unit] =
      new Separator[A] {
        type Left  = A
        type Right = Unit
        def separate(a: A): (A, Unit) = (a, ())
      }
  }

  trait SeparatorLowPriority2 {
    implicit def separate2[A, B]: Separator.WithTypes[(A, B), A, B] =
      new Separator[(A, B)] {
        type Left  = A
        type Right = B
        def separate(a: (A, B)): (A, B) = a
      }
  }

  def combine[L, R](l: L, r: R)(implicit c: Tuples[L, R]): c.Out     = c.combine(l, r)
  def separate[A](a: A)(implicit s: Separator[A]): (s.Left, s.Right) = s.separate(a)

  private[combinators] object TuplesMacros {

    private def isTuple(c: whitebox.Context)(tpe: c.universe.Type): Boolean = {
      val sym = tpe.typeSymbol
      sym.fullName.startsWith("scala.Tuple") && sym.fullName.matches("scala\\.Tuple[0-9]+")
    }

    private def tupleArity(c: whitebox.Context)(tpe: c.universe.Type): Int = {
      val name = tpe.typeSymbol.fullName
      name.stripPrefix("scala.Tuple").toInt
    }

    private def tupleElements(c: whitebox.Context)(tpe: c.universe.Type): List[c.universe.Type] =
      tpe.dealias.typeArgs

    def tuplesImpl[L: c.WeakTypeTag, R: c.WeakTypeTag](c: whitebox.Context): c.Tree = {
      import c.universe._

      val lType = weakTypeOf[L].dealias
      val rType = weakTypeOf[R].dealias

      val unitType = typeOf[Unit]

      if (lType =:= unitType) {
        q"""
          new _root_.zio.blocks.combinators.Tuples.Tuples[$lType, $rType] {
            type Out = $rType
            def combine(l: $lType, r: $rType): $rType = r
            def separate(out: $rType): ($lType, $rType) = ((), out)
          }
        """
      } else if (isTuple(c)(lType)) {
        val arity    = tupleArity(c)(lType)
        val elements = tupleElements(c)(lType)

        if (arity >= 22) {
          c.abort(c.enclosingPosition, s"Cannot combine Tuple$arity with another element: would exceed Tuple22 limit")
        }

        val newArity   = arity + 1
        val newTypes   = elements :+ rType
        val outType    = appliedType(symbolOf[(_, _)].owner.info.member(TypeName(s"Tuple$newArity")).asType, newTypes)
        val lAccessors = (1 to arity).map(i => q"l.${TermName(s"_$i")}")
        val allArgs    = lAccessors :+ q"r"

        val sepLAccessors = (1 to arity).map(i => q"out.${TermName(s"_$i")}")
        val sepR          = q"out.${TermName(s"_$newArity")}"

        q"""
          new _root_.zio.blocks.combinators.Tuples.Tuples[$lType, $rType] {
            type Out = $outType
            def combine(l: $lType, r: $rType): $outType = (..$allArgs)
            def separate(out: $outType): ($lType, $rType) = ((..$sepLAccessors), $sepR)
          }
        """
      } else {
        val outType = appliedType(typeOf[(_, _)].typeConstructor, List(lType, rType))
        q"""
          new _root_.zio.blocks.combinators.Tuples.Tuples[$lType, $rType] {
            type Out = $outType
            def combine(l: $lType, r: $rType): $outType = (l, r)
            def separate(out: $outType): ($lType, $rType) = out
          }
        """
      }
    }

    def separatorImpl[A: c.WeakTypeTag](c: whitebox.Context): c.Tree = {
      import c.universe._

      val aType = weakTypeOf[A].dealias

      if (isTuple(c)(aType)) {
        val arity    = tupleArity(c)(aType)
        val elements = tupleElements(c)(aType)

        if (arity == 2) {
          val leftType  = elements(0)
          val rightType = elements(1)
          q"""
            new _root_.zio.blocks.combinators.Tuples.Separator[$aType] {
              type Left = $leftType
              type Right = $rightType
              def separate(a: $aType): ($leftType, $rightType) = a
            }
          """
        } else {
          val leftTypes  = elements.init
          val rightType  = elements.last
          val leftArity  = arity - 1
          val leftType   = appliedType(symbolOf[(_, _)].owner.info.member(TypeName(s"Tuple$leftArity")).asType, leftTypes)
          val lAccessors = (1 until arity).map(i => q"a.${TermName(s"_$i")}")

          q"""
            new _root_.zio.blocks.combinators.Tuples.Separator[$aType] {
              type Left = $leftType
              type Right = $rightType
              def separate(a: $aType): ($leftType, $rightType) = ((..$lAccessors), a.${TermName(s"_$arity")})
            }
          """
        }
      } else {
        val unitType = typeOf[Unit]
        q"""
          new _root_.zio.blocks.combinators.Tuples.Separator[$aType] {
            type Left = $unitType
            type Right = $aType
            def separate(a: $aType): ($unitType, $aType) = ((), a)
          }
        """
      }
    }
  }
}
