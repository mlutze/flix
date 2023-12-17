/*
 * Copyright 2015-2016 Magnus Madsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.util

import ca.uwaterloo.flix.language.errors.{Recoverable, Unrecoverable}
import ca.uwaterloo.flix.util.Validation._
import org.scalatest.funsuite.AnyFunSuite


class TestValidation extends AnyFunSuite {

  test("map01") {
    val result = Validation.success("foo").map {
      case x => x.toUpperCase
    }
    assertResult(Validation.success("FOO"))(result)
  }

  test("map02") {
    val result = Validation.success("foo").map {
      case x => x.toUpperCase
    }.map {
      case y => y.reverse
    }
    assertResult(Validation.success("OOF"))(result)
  }

  test("map03") {
    val result = Validation.success("foo").map {
      case x => x.toUpperCase
    }.map {
      case y => y.reverse
    }.map {
      case z => z + z
    }
    assertResult(Validation.success("OOFOOF"))(result)
  }

  test("map04") {
    val result = Validation.success("abc").map {
      case x => x.length
    }.map {
      case y => y < 5
    }
    assertResult(Validation.success(true))(result)
  }

  test("map05") {
    val result = Validation.success[String, Exception]("abc").map {
      case x => x.charAt(1)
    }.map {
      case y => y + 3
    }.map {
      case z => z.toChar.toString
    }
    assertResult(Validation.success("e"))(result)
  }

  test("map06") {
    val result = SoftFailure("abc", LazyList.empty[Exception]).map {
      case x => x.length
    }.map {
      case y => y < 5
    }
    assertResult(SoftFailure(true, LazyList.empty[Exception]))(result)
  }

  test("map07") {
    val result = SoftFailure("abc", LazyList.empty[Exception]).map {
      case x => x.charAt(1)
    }.map {
      case y => y + 3
    }.map {
      case z => z.toChar.toString
    }
    assertResult(SoftFailure("e", LazyList.empty[Exception]))(result)
  }

  test("map08") {
    val ex = new RuntimeException()
    val result = SoftFailure("abc", LazyList(ex)).map {
      case x => x.length
    }.map {
      case y => y < 5
    }
    assertResult(SoftFailure(true, LazyList(ex)))(result)
  }

  test("map09") {
    val ex = new RuntimeException()
    val result = SoftFailure("abc", LazyList(ex)).map {
      case x => x.charAt(1)
    }.map {
      case y => y + 3
    }.map {
      case z => z.toChar.toString
    }
    assertResult(SoftFailure("e", LazyList(ex)))(result)
  }

  test("mapN01") {
    val result = mapN(Validation.success("foo"), Validation.success("foo")) {
      case (x, y) => x.toUpperCase.reverse + y.toUpperCase.reverse
    }
    assertResult(Validation.success("OOFOOF"))(result)
  }

  test("mapN02") {
    val result = mapN(Validation.success("foo"), Validation.success("foo"), SoftFailure("abc", LazyList.empty)) {
      case (x, y, _) => x.toUpperCase.reverse + y.toUpperCase.reverse
    }
    assertResult(SoftFailure("OOFOOF", LazyList.empty))(result)
  }

  test("mapN03") {
    val result = mapN(Validation.success("foo"), Validation.success("foo"), SoftFailure("abc", LazyList.empty)) {
      case (x, y, z) => x.toUpperCase.reverse + y.toUpperCase.reverse + z.toUpperCase.reverse
    }
    assertResult(SoftFailure("OOFOOFCBA", LazyList.empty))(result)
  }

  test("mapN04") {
    val ex = new RuntimeException()
    val result = mapN(Validation.success("foo"), Validation.success("foo"), SoftFailure("abc", LazyList(ex))) {
      case (x, y, z) => x.toUpperCase.reverse + y.toUpperCase.reverse + z.toUpperCase.reverse
    }
    assertResult(SoftFailure("OOFOOFCBA", LazyList(ex)))(result)
  }

  test("mapN05") {
    val result = mapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => x.toUpperCase.reverse
    }
    assertResult(SoftFailure("OOF", LazyList.empty))(result)
  }

  test("mapN06") {
    val ex = new RuntimeException()
    val result = mapN(SoftFailure("foo", LazyList(ex))) {
      case x => x.toUpperCase.reverse
    }
    assertResult(SoftFailure("OOF", LazyList(ex)))(result)
  }

  test("mapN07") {
    val ex = new RuntimeException()
    val result = mapN(HardFailure(LazyList(ex)): Validation[String, Exception]) {
      case x => x.toUpperCase.reverse
    }
    assertResult(HardFailure(LazyList(ex)))(result)
  }

  test("mapN08") {
    val result = mapN(Validation.success("foo"): Validation[String, Exception]) {
      case x => x.toUpperCase.reverse + x.toUpperCase.reverse
    }
    assertResult(Validation.success("OOFOOF"))(result)
  }

  test("flatMapN01") {
    val result = flatMapN(Validation.success("foo")) {
      case x => Validation.success(x.toUpperCase)
    }
    assertResult(Validation.success("FOO"))(result)
  }

  test("flatMapN02") {
    val result = flatMapN(Validation.success("foo")) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => Validation.success(z + z)
        }
      }
    }
    assertResult(Validation.success("OOFOOF"))(result)
  }

  test("flatMapN03") {
    val result = flatMapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => Validation.success((z + z))
        }
      }
    }
    assertResult(SoftFailure("OOFOOF", LazyList.empty[Exception]))(result)
  }

  test("flatMapN04") {
    val ex = new RuntimeException()
    val result = flatMapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => flatMapN(SoftFailure(x.toUpperCase, LazyList(ex))) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => Validation.success((z + z))
        }
      }
    }
    assertResult(SoftFailure("OOFOOF", LazyList(ex)))(result)
  }

  test("flatMapN05") {
    val ex = new RuntimeException()
    val result = flatMapN(Validation.success[String, Exception]("foo")) {
      case x => flatMapN(SoftFailure(x.toUpperCase, LazyList(ex))) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => Validation.success(z + z)
        }
      }
    }
    assertResult(SoftFailure("OOFOOF", LazyList(ex)))(result)
  }

  test("andThen03") {
    val ex = DummyUnrecoverable()
    val result = flatMapN(Validation.success[String, DummyUnrecoverable]("foo")) {
      case x => Validation.toHardFailure(ex)
    }
    assertResult(HardFailure(LazyList(ex)))(result)
  }

  test("andThen04") {
    val result = flatMapN(Validation.success("foo")) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => Validation.success(z + z)
        }
      }
    }
    assertResult(Validation.success("OOFOOF"))(result)
  }

  test("andThen05") {
    val result = flatMapN(Validation.success[String, Int]("foo")) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(HardFailure(LazyList(4, 5, 6))) {
          case z => HardFailure(LazyList(7, 8, 9))
        }
      }
    }
    assertResult(HardFailure(LazyList(4, 5, 6)))(result)
  }

  test("flatMap01") {
    val val1 = flatMapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => Validation.success(x.toUpperCase)
    }
    val val2 = flatMapN(val1) {
      case y => Validation.success(y.reverse)
    }
    val result = flatMapN(val2) {
      case z => Validation.success(z + z)
    }
    assertResult(SoftFailure("OOFOOF", LazyList.empty))(result)
  }

  test("flatMap02") {
    val result = flatMapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => Validation.success(z + z)
        }
      }
    }
    assertResult(SoftFailure("OOFOOF", LazyList.empty))(result)
  }

  test("flatMap03") {
    val ex = new RuntimeException()
    val result = flatMapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case z => SoftFailure[String, Exception](z + z, LazyList(ex))
        }
      }
    }
    assertResult(SoftFailure("OOFOOF", LazyList(ex)))(result)
  }

  test("flatMap04") {
    val ex = new RuntimeException()
    val result = flatMapN(SoftFailure("foo", LazyList.empty[Exception])) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(Validation.success(y.reverse)) {
          case _ => HardFailure[String, Exception](LazyList(ex))
        }
      }
    }
    assertResult(HardFailure(LazyList(ex)))(result)
  }

  test("flatMap05") {
    val ex1: Exception = new RuntimeException()
    val ex2: Exception = new RuntimeException()
    val result = flatMapN(SoftFailure("abc", LazyList(ex1))) {
      case x => flatMapN(Validation.success(x.toUpperCase)) {
        case y => flatMapN(SoftFailure[String, Exception](y.reverse, LazyList(ex2))) {
          case z => Validation.success(z + z)
        }
      }
    }
    assertResult(SoftFailure("CBACBA", LazyList(ex1, ex2)))(result)
  }

  test("flatMap06") {
    val ex1: Exception = new RuntimeException()
    val ex2: Exception = new RuntimeException()
    val result = flatMapN(Validation.success("abc")) {
      case x => flatMapN(SoftFailure(x.toUpperCase, LazyList(ex2))) {
        case y => flatMapN(SoftFailure(y.reverse, LazyList(ex1))) {
          case z => Success[String, Exception](z + z)
        }
      }
    }
    assertResult(SoftFailure("CBACBA", LazyList(ex2, ex1)))(result)
  }

  test("traverse01") {
    val result = traverse(List(1, 2, 3)) {
      case x => Validation.success(x + 1)
    }
    assertResult(Validation.success(List(2, 3, 4)))(result)
  }

  test("traverse02") {
    val result = traverse(List(1, 2, 3)) {
      case x => HardFailure(LazyList(42))
    }
    assertResult(HardFailure(LazyList(42, 42, 42)))(result)
  }

  test("traverse03") {
    val result = traverse(List(1, 2, 3)) {
      case x => if (x % 2 == 1) Validation.success(x) else HardFailure(LazyList(x))
    }
    assertResult(HardFailure(LazyList(2)))(result)
  }

  test("traverse04") {
    val result = traverse(List(1, 2, 3)) {
      case x => if (x % 2 == 1) SoftFailure(x, LazyList(-1)) else SoftFailure(-1, LazyList(x))
    }
    assertResult(SoftFailure(List(1, -1, 3), LazyList(-1, 2, -1)))(result)
  }

  test("traverse05") {
    val result = traverse(List(1, 2, 3)) {
      case x => if (x % 2 == 1) Validation.success(x) else SoftFailure(-1, LazyList(x))
    }
    assertResult(SoftFailure(List(1, -1, 3), LazyList(2)))(result)
  }

  test("traverse06") {
    val result = traverse(List(1, 2, 3, 4, 5)) {
      case x => if (x % 2 == 1) SoftFailure(x, LazyList(-x)) else HardFailure(LazyList(x))
    }
    assertResult(HardFailure(LazyList(-1, 2, -3, 4, -5)))(result)
  }

  test("foldRight01") {
    val result = foldRight(List(1, 1, 1))(Validation.success(10)) {
      case (x, acc) => Validation.success(acc - x)
    }
    assertResult(Validation.success(7))(result)
  }

  test("toSoftFailure01") {
    val e = DummyRecoverable()
    val v = Validation.toSoftFailure("abc", e)
    assertResult(SoftFailure("abc", LazyList(e)))(v)
  }

  test("toSoftFailure02") {
    val e = DummyRecoverable()
    val v = Validation.toSoftFailure("abc", e)
    val result = mapN(v) {
      case s => s.reverse
    }
    assertResult(SoftFailure("cba", LazyList(e)))(result)
  }

  test("toSoftFailure03") {
    val e = DummyRecoverable()
    val v = mapN(Validation.toSoftFailure("abc", e)) {
      case s => s.reverse
    }
    assertResult(SoftFailure("cba", LazyList(e)))(v)
  }

  test("recoverOne01") {
    val f: PartialFunction[DummyRecoverable, String] = (e: DummyRecoverable) => e.toString
    val v = Validation.success("abc").recoverOne(f)
    assertResult(Validation.success("abc"))(v)
  }

  test("recoverOne02") {
    val e = DummyRecoverable()
    val f: PartialFunction[DummyRecoverable, String] = (e: DummyRecoverable) => e.toString
    val r = Validation.toSoftFailure(e.toString, e).recoverOne(f)
    assertResult(Validation.toSoftFailure(e.toString, e))(r)
  }

  test("recoverOne03") {
    val ex = new RuntimeException()
    val f: PartialFunction[Exception, String] = (e: Exception) => e.toString
    val result = Validation.HardFailure(LazyList(ex, ex)).recoverOne(f)
    assertResult(Validation.HardFailure(LazyList(ex, ex)))(result)
  }

  trait DummyError

  case class DummyRecoverable() extends DummyError with Recoverable

  case class DummyUnrecoverable() extends DummyError with Unrecoverable
}
