package typechecker

abstract class Goal<G : Goal<G>> {
  /** Whether [other] poses the same problem: the same statement in the same context, so the same steps prove it. */
  open fun isSameProblem(other: G): Boolean = this == other
}
