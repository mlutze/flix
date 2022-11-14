/*
 * Copyright 2020 Matthew Lutze
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

package ca.uwaterloo.flix.language.phase.unification

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.Ast.ClassContext
import ca.uwaterloo.flix.language.ast.{Ast, RigidityEnv, Symbol, Type}
import ca.uwaterloo.flix.util.{InternalCompilerException, Validation}
import ca.uwaterloo.flix.util.Validation.{ToFailure, ToSuccess}

import scala.annotation.tailrec

object ClassEnvironment {


  /**
    * Returns success iff type constraints `tconstrs0` entail type constraint `tconstr`, under class environment `instances`.
    * That is, `tconstr` is true if all of `tconstrs0` are true.
    */
  // MATT THIH says that toncstrs0 should always be in HNF so checking for byInst is a waste.
  def entail(tconstrs0: List[Ast.TypeConstraint], tconstr: Ast.TypeConstraint, classEnv: Map[Symbol.ClassSym, Ast.ClassContext], renv: RigidityEnv)(implicit flix: Flix): Validation[Substitution, UnificationError] = {

    // All the type constraints entailed transitively by `tconstrs0`
    val transitiveTconstrs = tconstrs0.flatMap(byTypeConstraint(_, classEnv))

    // The type constraints that match `tconstr`
    val matchingTconstrs = transitiveTconstrs.filter(baseMatch(tconstr, _))

    matchingTconstrs match {
      // Case 1: nothing matches. go byInst instead
      case Nil =>
        // see if there is an instance matching tconstr and all of the instance's constraints are entailed by tconstrs0
        for {
          tconstrs <- byInst(tconstr, classEnv, renv)
          subst <- Validation.fold(tconstrs, Substitution.empty) {
            case (acc, tconstr) => entail(tconstrs0, acc(tconstr), classEnv, renv).map(_ @@ acc)
          }
        } yield subst

      // Case 2: tconstrs0 entail tconstr if tconstr matches any (transitive) type constraint of the classes in tconstrs0
      case Ast.TypeConstraint(_, args1, _) :: _ => tconstr match {
        case Ast.TypeConstraint(_, args0, _) =>
          Unification.unifyAll(args0, args1, renv).toValidation
        // MATT can safely remove environment tvars from the subst
      }
      // Case 3: multiple matches. Idk I'll deal with this if it comes up
//      case _ :: _ :: _ => ???
      // MATT :|
    }

    // MATT Unify all the matches (probably need new error for inconsistent tconstrs
    // MATT Unify with the tconstr
    // MATT if ok: send substitution
    // MATT if not ok:
    // MATT go by inst


    // MATT have to instantiate the type class before unifying else substitutions will conflict
  }

  /**
    * Returns true iff the two type constraints have the same head and final (determining) argument.
    */
  private def baseMatch(tconstr1: Ast.TypeConstraint, tconstr2: Ast.TypeConstraint): Boolean = (tconstr1, tconstr2) match {
    case (Ast.TypeConstraint(head1, _ :+ arg1, _), Ast.TypeConstraint(head2, _ :+ arg2, _)) => head1.sym == head2.sym && arg1 == arg2
    case _ => throw InternalCompilerException("unexpected empty type constraint")
  }

  /**
    * Returns true iff type constraint `tconstr1` entails tconstr2 under class environment `classEnv`.
    */
  def entails(tconstr1: Ast.TypeConstraint, tconstr2: Ast.TypeConstraint, classEnv: Map[Symbol.ClassSym, Ast.ClassContext]): Boolean = {
    val superClasses = byTypeConstraint(tconstr1, classEnv)
    superClasses.contains(tconstr2)
  }

  /**
    * Returns true iff the given type constraint holds under the given class environment.
    */
  def holds(tconstr: Ast.TypeConstraint, classEnv: Map[Symbol.ClassSym, Ast.ClassContext], renv: RigidityEnv)(implicit flix: Flix): Boolean = {
    byInst(tconstr, classEnv, renv) match {
      case Validation.Success(_) => true
      case Validation.Failure(_) => false
    }
  }

  /**
    * Removes the type constraints which are entailed by the others in the list.
    */
  private def simplify(tconstrs0: List[Ast.TypeConstraint], classEnv: Map[Symbol.ClassSym, Ast.ClassContext], renv: RigidityEnv)(implicit flix: Flix): List[Ast.TypeConstraint] = {

    @tailrec
    def loop(tconstrs0: List[Ast.TypeConstraint], acc: List[Ast.TypeConstraint]): List[Ast.TypeConstraint] = tconstrs0 match {
      // Case 0: no tconstrs left to process, we're done
      case Nil => acc
      case head :: tail => entail(acc ++ tail, head, classEnv, renv) match {
        // Case 1: `head` is entailed by the other type constraints, skip it
        case Validation.Success(_) => loop(tail, acc)
        // Case 2: `head` is not entailed, add it to the list
        case Validation.Failure(_) => loop(tail, head :: acc)
      }
    }

    loop(tconstrs0, Nil)
  }

  /**
    * Normalizes a list of type constraints, converting to head-normal form and removing semantic duplicates.
    */
  def reduce(tconstrs0: List[Ast.TypeConstraint], classEnv: Map[Symbol.ClassSym, Ast.ClassContext], renv: RigidityEnv)(implicit flix: Flix): Validation[List[Ast.TypeConstraint], UnificationError] = {
    val tconstrs1 = tconstrs0.map {
      case Ast.TypeConstraint(head, tpes, loc) => Ast.TypeConstraint(head, tpes.map(Type.eraseAliases), loc)
    }
    for {
      tconstrs <- Validation.sequence(tconstrs1.map(toHeadNormalForm(_, classEnv, renv)))
    } yield simplify(tconstrs.flatten, classEnv, renv)
  }

  /**
    * Converts the type constraint to head-normal form, i.e. `a[X1, Xn]`, where `a` is a variable and `n >= 0`.
    */
  private def toHeadNormalForm(tconstr: Ast.TypeConstraint, classEnv: Map[Symbol.ClassSym, ClassContext], renv: RigidityEnv)(implicit flix: Flix): Validation[List[Ast.TypeConstraint], UnificationError] = {
    if (isHeadNormalForm(tconstr.arg.last)) {
      List(tconstr).toSuccess
    } else {
      byInst(tconstr, classEnv, renv)
    }
  }

  /**
    * Returns the list of constraints that hold if the given constraint `tconstr` holds, using the constraints on available instances.
    */
  private def byInst(tconstr: Ast.TypeConstraint, classEnv: Map[Symbol.ClassSym, Ast.ClassContext], renv0: RigidityEnv)(implicit flix: Flix): Validation[List[Ast.TypeConstraint], UnificationError] = {
    val matchingInstances = classEnv.get(tconstr.head.sym).map(_.instances).getOrElse(Nil)

    // Must rigidify the primary type
    val renv = tconstr.arg.last.typeVars.foldLeft(renv0) {
      case (acc, Type.Var(sym, _)) => acc.markRigid(sym)
      case (acc, _) => acc
    }

    def tryInst(inst: Ast.Instance): Validation[List[Ast.TypeConstraint], UnificationError] = {

      for {
        subst <- Unification.unifyAll(tconstr.arg, inst.tpes, renv).toValidation
        //        subst <- Unification.unifyTypes(tconstr.arg.last, inst.tpes.last, renv).toValidation
      } yield inst.tconstrs.map(subst(_))
    }

    val tconstrGroups = matchingInstances.map(tryInst).collect {
      case Validation.Success(result) => result
    }

    tconstrGroups match {
      case Nil => UnificationError.NoMatchingInstance(tconstr).toFailure
      case tconstrs :: Nil =>
        // apply the base tconstr location to the new tconstrs
        tconstrs.map(_.copy(loc = tconstr.loc)).toSuccess
      case _ :: _ :: _ =>
        // Multiple matching instances: This will be caught in the Instances phase.
        // We return Nil here because there is no canonical set of constraints,
        // so we stop adding constraints and let the later phase take care of it.
        Nil.toSuccess
    }
  }

  /**
    * Returns the list of constraints that hold if the given constraint `tconstr` holds, using the super classes of the constraint.
    *
    * E.g. if we have 3 classes: `A`, `B`, `C` where
    * - `A` extends `B`
    * - `B` extends `C`
    * Then for the constraint `t : A`, we return:
    * - `t : A` (given)
    * - `t : B` (because `B` is a super class of `A`)
    * - `t : C` (because `C` is a super class of `B`, and transitively a super class of `A`)
    *
    */
  // MATT update docs
  private def byTypeConstraint(tconstr: Ast.TypeConstraint, classEnv: Map[Symbol.ClassSym, Ast.ClassContext]): List[Ast.TypeConstraint] = {

    // Get the constraints that are direct constraints of the class in `tconstr`
    val directTconstrs = classEnv.get(tconstr.head.sym).map(_.tconstrs).getOrElse(Nil)

    val tparams = classEnv(tconstr.head.sym).tparams // MATT we assume it's in the classEnv. Is that safe?

    val subst = Substitution(tparams.zip(tconstr.arg).toMap)

    val substedTconstrs = directTconstrs.map(subst.apply)

    // Walk the super class tree.
    // There may be duplicates, but this will terminate since super classes must be acyclic.
    tconstr :: substedTconstrs.flatMap(byTypeConstraint(_, classEnv)) // MATT are duplicates still OK?
  }

  /**
    * Returns true iff this type is in head-normal form.
    */
  private def isHeadNormalForm(tpe: Type): Boolean = {
    tpe.typeConstructor.isEmpty
  }
}
