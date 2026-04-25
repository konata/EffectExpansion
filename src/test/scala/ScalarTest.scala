package side.effect.free

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import scala.collection.mutable

import soot.jimple.*
import soot.jimple.internal.JimpleLocal
import soot.{ArrayType, ByteType, CharType, DoubleType, FloatType, IntType, LongType, ShortType, SootMethod, VoidType}

class ScalarTest extends AnyFlatSpec with Matchers {

  // Scope backed by a hollow SootMethod — needle is lazy so no body needed
  private def scope(locals: (JimpleLocal, Types)*): Scope = {
    val method = new SootMethod("test", java.util.Collections.emptyList(), VoidType.v())
    val s = Scope(mutable.Map(), None, method, Array(), None)
    locals.foreach { case (l, t) => s.local(l) = t }
    s
  }

  private val S = scope()

  // ── resolve ────────────────────────────────────────────────────────────────

  "Scope.resolve" should "unwrap int constants" in {
    S.resolve(IntConstant.v(42)) shouldBe Some(Types.Ints(42))
  }
  it should "unwrap long constants" in {
    S.resolve(LongConstant.v(99L)) shouldBe Some(Types.Longs(99L))
  }
  it should "unwrap float constants" in {
    S.resolve(FloatConstant.v(1.5f)) shouldBe Some(Types.Floats(1.5f))
  }
  it should "unwrap double constants" in {
    S.resolve(DoubleConstant.v(2.5)) shouldBe Some(Types.Doubles(2.5))
  }
  it should "unwrap string constants" in {
    S.resolve(StringConstant.v("hi")) shouldBe Some(Types.Strings("hi"))
  }
  it should "unwrap null constants" in {
    S.resolve(NullConstant.v()) shouldBe Some(Types.Undefined)
  }
  it should "look up locals" in {
    val x = new JimpleLocal("x", IntType.v())
    val s = scope(x -> Types.Ints(7))
    s.resolve(x) shouldBe Some(Types.Ints(7))
  }
  it should "return None for unknown locals" in {
    val x = new JimpleLocal("x", IntType.v())
    S.resolve(x) shouldBe None
  }

  // ── arithmetic ─────────────────────────────────────────────────────────────

  "evalValue" should "add ints" in {
    evalValue(Jimple.v().newAddExpr(IntConstant.v(3), IntConstant.v(5)), S) shouldBe Some(Types.Ints(8))
  }
  it should "subtract ints" in {
    evalValue(Jimple.v().newSubExpr(IntConstant.v(10), IntConstant.v(4)), S) shouldBe Some(Types.Ints(6))
  }
  it should "multiply ints" in {
    evalValue(Jimple.v().newMulExpr(IntConstant.v(3), IntConstant.v(7)), S) shouldBe Some(Types.Ints(21))
  }
  it should "divide ints" in {
    evalValue(Jimple.v().newDivExpr(IntConstant.v(10), IntConstant.v(3)), S) shouldBe Some(Types.Ints(3))
  }
  it should "mod ints" in {
    evalValue(Jimple.v().newRemExpr(IntConstant.v(10), IntConstant.v(3)), S) shouldBe Some(Types.Ints(1))
  }
  it should "add longs" in {
    evalValue(Jimple.v().newAddExpr(LongConstant.v(2L), LongConstant.v(3L)), S) shouldBe Some(Types.Longs(5L))
  }
  it should "add floats" in {
    evalValue(Jimple.v().newAddExpr(FloatConstant.v(1.5f), FloatConstant.v(0.5f)), S) shouldBe Some(Types.Floats(2.0f))
  }
  it should "add doubles" in {
    evalValue(Jimple.v().newAddExpr(DoubleConstant.v(1.0), DoubleConstant.v(2.0)), S) shouldBe Some(Types.Doubles(3.0))
  }
  it should "negate int" in {
    evalValue(Jimple.v().newNegExpr(IntConstant.v(5)), S) shouldBe Some(Types.Ints(-5))
  }
  it should "negate long" in {
    evalValue(Jimple.v().newNegExpr(LongConstant.v(5L)), S) shouldBe Some(Types.Longs(-5L))
  }
  it should "negate float" in {
    evalValue(Jimple.v().newNegExpr(FloatConstant.v(3.0f)), S) shouldBe Some(Types.Floats(-3.0f))
  }

  // ── bitwise ────────────────────────────────────────────────────────────────

  it should "and ints" in {
    evalValue(Jimple.v().newAndExpr(IntConstant.v(0b1010), IntConstant.v(0b1100)), S) shouldBe Some(Types.Ints(0b1000))
  }
  it should "or ints" in {
    evalValue(Jimple.v().newOrExpr(IntConstant.v(0b1010), IntConstant.v(0b0101)), S) shouldBe Some(Types.Ints(0b1111))
  }
  it should "xor ints" in {
    evalValue(Jimple.v().newXorExpr(IntConstant.v(0b1111), IntConstant.v(0b1010)), S) shouldBe Some(Types.Ints(0b0101))
  }
  it should "and longs" in {
    evalValue(Jimple.v().newAndExpr(LongConstant.v(0xFFL), LongConstant.v(0x0FL)), S) shouldBe Some(Types.Longs(0x0FL))
  }

  // ── shifts ─────────────────────────────────────────────────────────────────

  it should "shl int" in {
    evalValue(Jimple.v().newShlExpr(IntConstant.v(1), IntConstant.v(4)), S) shouldBe Some(Types.Ints(16))
  }
  it should "shr int" in {
    evalValue(Jimple.v().newShrExpr(IntConstant.v(-16), IntConstant.v(2)), S) shouldBe Some(Types.Ints(-4))
  }
  it should "ushr int" in {
    evalValue(Jimple.v().newUshrExpr(IntConstant.v(-1), IntConstant.v(28)), S) shouldBe Some(Types.Ints(0xF))
  }
  it should "shl long" in {
    evalValue(Jimple.v().newShlExpr(LongConstant.v(1L), IntConstant.v(10)), S) shouldBe Some(Types.Longs(1024L))
  }

  // ── comparisons ────────────────────────────────────────────────────────────

  it should "eq ints (true)" in {
    evalValue(Jimple.v().newEqExpr(IntConstant.v(3), IntConstant.v(3)), S) shouldBe Some(Types.Ints(1))
  }
  it should "eq ints (false)" in {
    evalValue(Jimple.v().newEqExpr(IntConstant.v(3), IntConstant.v(4)), S) shouldBe Some(Types.Ints(0))
  }
  it should "ne ints" in {
    evalValue(Jimple.v().newNeExpr(IntConstant.v(3), IntConstant.v(4)), S) shouldBe Some(Types.Ints(1))
  }
  it should "lt ints (true)" in {
    evalValue(Jimple.v().newLtExpr(IntConstant.v(2), IntConstant.v(5)), S) shouldBe Some(Types.Ints(1))
  }
  it should "lt ints (false)" in {
    evalValue(Jimple.v().newLtExpr(IntConstant.v(5), IntConstant.v(2)), S) shouldBe Some(Types.Ints(0))
  }
  it should "ge ints" in {
    evalValue(Jimple.v().newGeExpr(IntConstant.v(5), IntConstant.v(5)), S) shouldBe Some(Types.Ints(1))
  }

  // ── long comparison ────────────────────────────────────────────────────────

  it should "cmp longs (greater)" in {
    evalValue(Jimple.v().newCmpExpr(LongConstant.v(10L), LongConstant.v(5L)), S) shouldBe Some(Types.Ints(1))
  }
  it should "cmp longs (equal)" in {
    evalValue(Jimple.v().newCmpExpr(LongConstant.v(5L), LongConstant.v(5L)), S) shouldBe Some(Types.Ints(0))
  }
  it should "cmp longs (less)" in {
    evalValue(Jimple.v().newCmpExpr(LongConstant.v(3L), LongConstant.v(5L)), S) shouldBe Some(Types.Ints(-1))
  }

  // ── float comparison with NaN ──────────────────────────────────────────────

  it should "cmpg floats (NaN → +1)" in {
    evalValue(Jimple.v().newCmpgExpr(FloatConstant.v(Float.NaN), FloatConstant.v(1.0f)), S) shouldBe Some(Types.Ints(1))
  }
  it should "cmpl floats (NaN → -1)" in {
    evalValue(Jimple.v().newCmplExpr(FloatConstant.v(Float.NaN), FloatConstant.v(1.0f)), S) shouldBe Some(Types.Ints(-1))
  }
  it should "cmpg floats (normal)" in {
    evalValue(Jimple.v().newCmpgExpr(FloatConstant.v(2.0f), FloatConstant.v(1.0f)), S) shouldBe Some(Types.Ints(1))
  }
  it should "cmpl doubles (NaN → -1)" in {
    evalValue(Jimple.v().newCmplExpr(DoubleConstant.v(Double.NaN), DoubleConstant.v(1.0)), S) shouldBe Some(Types.Ints(-1))
  }

  // ── local operands ─────────────────────────────────────────────────────────

  it should "read locals as operands" in {
    val x = new JimpleLocal("x", IntType.v())
    val y = new JimpleLocal("y", IntType.v())
    val s = scope(x -> Types.Ints(10), y -> Types.Ints(3))
    evalValue(Jimple.v().newAddExpr(x, y), s) shouldBe Some(Types.Ints(13))
    evalValue(Jimple.v().newMulExpr(x, y), s) shouldBe Some(Types.Ints(30))
  }
  it should "return None when a local is unbound" in {
    val x = new JimpleLocal("x", IntType.v())
    evalValue(Jimple.v().newNegExpr(x), S) shouldBe None
  }

  // ── type casts ─────────────────────────────────────────────────────────────

  it should "cast int to long" in {
    evalValue(Jimple.v().newCastExpr(IntConstant.v(42), LongType.v()), S) shouldBe Some(Types.Longs(42L))
  }
  it should "cast int to float" in {
    evalValue(Jimple.v().newCastExpr(IntConstant.v(3), FloatType.v()), S) shouldBe Some(Types.Floats(3.0f))
  }
  it should "cast int to double" in {
    evalValue(Jimple.v().newCastExpr(IntConstant.v(3), DoubleType.v()), S) shouldBe Some(Types.Doubles(3.0))
  }
  it should "cast long to int (narrowing)" in {
    evalValue(Jimple.v().newCastExpr(LongConstant.v(300L), IntType.v()), S) shouldBe Some(Types.Ints(300))
  }
  it should "cast double to float (narrowing)" in {
    evalValue(Jimple.v().newCastExpr(DoubleConstant.v(1.5), FloatType.v()), S) shouldBe Some(Types.Floats(1.5f))
  }
  it should "cast int to byte (truncating)" in {
    evalValue(Jimple.v().newCastExpr(IntConstant.v(300), ByteType.v()), S) shouldBe Some(Types.Bytes(300.toByte))
  }
  it should "cast int to short" in {
    evalValue(Jimple.v().newCastExpr(IntConstant.v(1000), ShortType.v()), S) shouldBe Some(Types.Shorts(1000.toShort))
  }
  it should "cast int to char" in {
    evalValue(Jimple.v().newCastExpr(IntConstant.v(65), CharType.v()), S) shouldBe Some(Types.Chars('A'))
  }

  // ── array operations ───────────────────────────────────────────────────────

  it should "create a new array with NewArrayExpr" in {
    val result = evalValue(Jimple.v().newNewArrayExpr(IntType.v(), IntConstant.v(3)), S)
    result shouldBe Some(Types.Arrays(scala.collection.mutable.ArrayBuffer(Types.Undefined, Types.Undefined, Types.Undefined)))
  }
  it should "get array length" in {
    val arr = new JimpleLocal("arr", ArrayType.v(IntType.v(), 1))
    val s   = scope(arr -> Types.Arrays(scala.collection.mutable.ArrayBuffer(Types.Ints(1), Types.Ints(2), Types.Ints(3))))
    evalValue(Jimple.v().newLengthExpr(arr), s) shouldBe Some(Types.Ints(3))
  }
  it should "read an array element via ArrayRef" in {
    val arr = new JimpleLocal("arr", ArrayType.v(IntType.v(), 1))
    val s   = scope(arr -> Types.Arrays(scala.collection.mutable.ArrayBuffer(Types.Ints(10), Types.Ints(20))))
    evalValue(Jimple.v().newArrayRef(arr, IntConstant.v(1)), s) shouldBe Some(Types.Ints(20))
  }
  it should "return None for out-of-bounds array access" in {
    val arr = new JimpleLocal("arr", ArrayType.v(IntType.v(), 1))
    val s   = scope(arr -> Types.Arrays(scala.collection.mutable.ArrayBuffer(Types.Ints(10))))
    evalValue(Jimple.v().newArrayRef(arr, IntConstant.v(5)), s) shouldBe None
  }
}
