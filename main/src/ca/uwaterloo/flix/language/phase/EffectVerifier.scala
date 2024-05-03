package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.language.ast.TypedAst.{Def, Expr, Root}
import ca.uwaterloo.flix.language.ast.{SourceLocation, Symbol, Type}
import ca.uwaterloo.flix.util.collection.Chain

object EffectVerifier {
  def run(root: Root): Unit = {
    root.defs.foreach {
      case (sym, defn) => visitDef(defn)
    }
  }

  def visitDef(defn: Def): Unit = {
    val boundVars = defn.spec.tparams.map(_.sym).toSet
    for {
      (tpe, loc) <- findFreeVars(defn.exp)(boundVars).toSeq
    } {
      println(defn.sym.toString + " @ " + loc.toString + " : " + tpe)
    }
  }

  def findFreeVars(exp0: Expr)(implicit boundVars: Set[Symbol.KindedTypeVarSym]): Chain[(Type, SourceLocation)] = {
    val head = if (exp0.tpe.typeVars.exists { t => !boundVars.contains(t.sym) }) {
      Chain((exp0.tpe, exp0.loc))
    } else {
      Chain()
    }
    val tail = exp0 match {
      case Expr.Cst(cst, tpe, loc) => Chain.empty
      case Expr.Var(sym, tpe, loc) => Chain.empty
      case Expr.Def(sym, tpe, loc) => Chain.empty
      case Expr.Sig(sym, tpe, loc) => Chain.empty
      case Expr.Hole(sym, tpe, loc) => Chain.empty
      case Expr.HoleWithExp(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.OpenAs(symUse, exp, tpe, loc) => findFreeVars(exp)
      case Expr.Use(sym, alias, exp, loc) => findFreeVars(exp)
      case Expr.Lambda(fparam, exp, tpe, loc) => findFreeVars(exp)
      case Expr.Apply(exp, exps, tpe, eff, loc) => findFreeVars(exp) ++ Chain.from(exps.map(findFreeVars).flatMap(_.toSeq))
      case Expr.Unary(sop, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.Binary(sop, exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.Let(sym, mod, exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.LetRec(sym, ann, mod, exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.Region(tpe, loc) => Chain.empty
      case Expr.Scope(sym, regionVar, exp, tpe, eff, loc) => findFreeVars(exp)(boundVars + regionVar.sym)
      case Expr.IfThenElse(exp1, exp2, exp3, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2) ++ findFreeVars(exp3)
      case Expr.Stm(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.Discard(exp, eff, loc) => findFreeVars(exp)
      case Expr.Match(exp, rules, tpe, eff, loc) => findFreeVars(exp) ++ Chain.from(rules.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq)) ++ Chain.from(rules.flatMap(rule => rule.guard).map(findFreeVars).flatMap(_.toSeq))
      case Expr.TypeMatch(exp, rules, tpe, eff, loc) => findFreeVars(exp) ++ Chain.from(rules.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq))
      case Expr.RestrictableChoose(star, exp, rules, tpe, eff, loc) => findFreeVars(exp) ++ Chain.from(rules.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq))
      case Expr.Tag(sym, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.RestrictableTag(sym, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.Tuple(elms, tpe, eff, loc) => Chain.from(elms.map(findFreeVars).flatMap(_.toSeq))
      case Expr.RecordEmpty(tpe, loc) => Chain.empty
      case Expr.RecordSelect(exp, label, tpe, eff, loc) => findFreeVars(exp)
      case Expr.RecordExtend(label, exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.RecordRestrict(label, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.ArrayLit(exps, exp, tpe, eff, loc) => Chain.from(exps.map(findFreeVars).flatMap(_.toSeq)) ++ findFreeVars(exp)
      case Expr.ArrayNew(exp1, exp2, exp3, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2) ++ findFreeVars(exp3)
      case Expr.ArrayLoad(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.ArrayLength(exp, eff, loc) => findFreeVars(exp)
      case Expr.ArrayStore(exp1, exp2, exp3, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2) ++ findFreeVars(exp3)
      case Expr.VectorLit(exps, tpe, eff, loc) => Chain.from(exps.map(findFreeVars).flatMap(_.toSeq))
      case Expr.VectorLoad(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.VectorLength(exp, loc) => findFreeVars(exp)
      case Expr.Ref(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.Deref(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.Assign(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.Ascribe(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.InstanceOf(exp, clazz, loc) => findFreeVars(exp)
      case Expr.CheckedCast(cast, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.UncheckedCast(exp, declaredType, declaredEff, tpe, eff, loc) => findFreeVars(exp)
      case Expr.UncheckedMaskingCast(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.Without(exp, effUse, tpe, eff, loc) => findFreeVars(exp)
      case Expr.TryCatch(exp, rules, tpe, eff, loc) => findFreeVars(exp) ++ Chain.from(rules.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq))
      case Expr.TryWith(exp, effUse, rules, tpe, eff, loc) => findFreeVars(exp) ++ Chain.from(rules.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq))
      case Expr.Do(op, exps, tpe, eff, loc) => Chain.from(exps.map(findFreeVars).flatMap(_.toSeq))
      case Expr.InvokeConstructor(constructor, exps, tpe, eff, loc) => Chain.from(exps.map(findFreeVars).flatMap(_.toSeq))
      case Expr.InvokeMethod(method, exp, exps, tpe, eff, loc) => Chain.from(exps.map(findFreeVars).flatMap(_.toSeq))
      case Expr.InvokeStaticMethod(method, exps, tpe, eff, loc) => Chain.from(exps.map(findFreeVars).flatMap(_.toSeq))
      case Expr.GetField(field, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.PutField(field, exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.GetStaticField(field, tpe, eff, loc) => Chain.empty
      case Expr.PutStaticField(field, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.NewObject(name, clazz, tpe, eff, methods, loc) => Chain.from(methods.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq))
      case Expr.NewChannel(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.GetChannel(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.PutChannel(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.SelectChannel(rules, default, tpe, eff, loc) => Chain.from(rules.map(rule => rule.exp).map(findFreeVars).flatMap(_.toSeq)) // TODO ignoring default
      case Expr.Spawn(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.ParYield(frags, exp, tpe, eff, loc) => findFreeVars(exp) // TODO ignoring frags
      case Expr.Lazy(exp, tpe, loc) => findFreeVars(exp)
      case Expr.Force(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.FixpointConstraintSet(cs, tpe, loc) => Chain.empty // TODO ignoring
      case Expr.FixpointLambda(pparams, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.FixpointMerge(exp1, exp2, tpe, eff, loc) => findFreeVars(exp1) ++ findFreeVars(exp2)
      case Expr.FixpointSolve(exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.FixpointFilter(pred, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.FixpointInject(exp, pred, tpe, eff, loc) => findFreeVars(exp)
      case Expr.FixpointProject(pred, exp, tpe, eff, loc) => findFreeVars(exp)
      case Expr.Error(m, tpe, eff) => Chain.empty
    }

    head ++ tail
  }
}
