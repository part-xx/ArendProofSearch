package typechecker.cli

import typechecker.Goal

class PlainTextGoal(
    val id: String,
    val expectedType: String,
    val contextBindings: List<ContextBinding>,
    val moduleDef: String
) : Goal<PlainTextGoal>() {

    override fun toString(): String {
        val ctx = if (contextBindings.isNotEmpty()) {
            contextBindings.joinToString(", ") { "${it.name} : ${it.type}" }
        } else ""
        return "Goal[$id] $expectedType" + if (ctx.isNotEmpty()) " | $ctx" else ""
    }

    /**
     * Semantic identity: a goal is its lemma, expected type, and local context —
     * NOT its positional [id], which is per-proof and differs across branches for
     * the same subgoal. This lets the same subgoal arising in different branches
     * share one entry in goal-keyed maps (e.g. memoized steps).
     *
     * Contexts compare as ordered binding lists, exactly as the typechecker reports
     * them; two occurrences of the same subgoal arise from the same path and agree.
     */
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is PlainTextGoal) return false
        return moduleDef == other.moduleDef &&
                expectedType == other.expectedType &&
                contextBindings == other.contextBindings
    }

    override fun hashCode(): Int {
        var result = moduleDef.hashCode()
        result = 31 * result + expectedType.hashCode()
        result = 31 * result + contextBindings.hashCode()
        return result
    }
}
