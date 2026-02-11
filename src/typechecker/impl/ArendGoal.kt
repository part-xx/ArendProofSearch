package typechecker.impl

import org.arend.core.expr.Expression
import org.arend.term.concrete.Concrete
import org.arend.typechecking.visitor.CheckTypeVisitor
import typechecker.Goal


class ArendGoal(val expectedType: Expression, val typechecker: CheckTypeVisitor, val sourceNode: Concrete.Expression): Goal() {

}