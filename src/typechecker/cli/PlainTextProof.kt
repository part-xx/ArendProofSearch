package typechecker.cli

import typechecker.Proof

class PlainTextProof(
    private val cli: CliApi,
    val moduleDef: String,
    val proofText: String,
    private val cachedGoals: List<PlainTextGoal>? = null
) : Proof<PlainTextGoal> {

    override fun goals(): List<PlainTextGoal> {
        if (cachedGoals != null) return cachedGoals
        val response = cli.findGoals(moduleDef)
        return response.goals.map { goal ->
            PlainTextGoal(
                id = goal.id,
                expectedType = goal.expectedType,
                contextBindings = goal.context,
                moduleDef = moduleDef
            )
        }
    }

    override fun replaceGoal(goal: PlainTextGoal, proof: Proof<PlainTextGoal>): Proof<PlainTextGoal>? {
        val replacement = (proof as? PlainTextProof)?.proofText ?: return null
        val response = cli.applyStep(moduleDef, goal.id, replacement)
        if (!response.success) return null

        val newGoals = response.goals.map { g ->
            PlainTextGoal(
                id = g.id,
                expectedType = g.expectedType,
                contextBindings = g.context,
                moduleDef = moduleDef
            )
        }
        return PlainTextProof(cli, moduleDef, response.proof, newGoals)
    }

    override fun toString(): String = proofText

    companion object {
        fun initial(cli: CliApi, moduleDef: String): PlainTextProof {
            val response = cli.findGoals(moduleDef)
            val goals = response.goals.map { goal ->
                PlainTextGoal(
                    id = goal.id,
                    expectedType = goal.expectedType,
                    contextBindings = goal.context,
                    moduleDef = moduleDef
                )
            }
            return PlainTextProof(cli, moduleDef, "{?}", goals)
        }
    }
}
