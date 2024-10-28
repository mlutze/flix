/*
 * Copyright 2022 Matthew Lutze
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
package ca.uwaterloo.flix.util.collection

object MapOps {

  /**
    * Applies `f` to each of the values in the given map.
    *
    * Replaces the deprecated [[Map.mapValues]].
    */
  def mapValues[K, V1, V2](m: Map[K, V1])(f: V1 => V2): Map[K, V2] = {
    m.map {
      case (k, v) => (k, f(v))
    }
  }

  /**
    * Combines the two maps with the given function.
    *
    * If a key is present in only one of the maps, then that map's value is used.
    * If a key is present in both maps, the function is used to combine the respective values.
    */
  def unionWith[K, V](m1: Map[K, V], m2: Map[K, V])(f: (V, V) => V): Map[K, V] = {
    val keys = m1.keySet ++ m2.keySet
    keys.map {
      case key =>
        (m1.get(key), m2.get(key)) match {
          case (None, None) => throw new AssertionError("unexpected unknown key")
          case (Some(value), None) => key -> value
          case (None, Some(value)) => key -> value
          case (Some(value1), Some(value2)) => key -> f(value1, value2)
        }
    }.toMap
  }

  /**
    * Adds the mapping (k1 -> (k2 -> v)) to the nested map.
    */
  def addNested[K1, K2, V](m: Map[K1, Map[K2, V]], k1: K1, k2: K2, v: V): Map[K1, Map[K2, V]] = {
    val oldInnerMap = m.getOrElse(k1, Map.empty)
    val newInnerMap = oldInnerMap + (k2 -> v)
    m + (k1 -> newInnerMap)
  }
}
