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

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is PlainTextGoal) return false
        return id == other.id && moduleDef == other.moduleDef
    }

    override fun hashCode(): Int = id.hashCode() * 31 + moduleDef.hashCode()
}
