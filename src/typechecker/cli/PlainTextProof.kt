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
        val goalIndex = goal.id.toIntOrNull() ?: return null
        val newBody = replaceNthGoal(proofText, goalIndex, replacement) ?: return null

        val response = cli.applyStep(moduleDef, newBody)
        if (!response.success) return null

        val newGoals = response.goals.map { g ->
            PlainTextGoal(
                id = g.id,
                expectedType = g.expectedType,
                contextBindings = g.context,
                moduleDef = moduleDef
            )
        }
        return PlainTextProof(cli, moduleDef, newBody, newGoals)
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

        fun replaceNthGoal(text: String, n: Int, replacement: String): String? {
            var count = 0
            var i = 0
            while (i <= text.length - 3) {
                if (text[i] == '{' && text[i + 1] == '?' && text[i + 2] == '}') {
                    if (count == n) {
                        return text.substring(0, i) + replacement + text.substring(i + 3)
                    }
                    count++
                    i += 3
                } else {
                    i++
                }
            }
            return null
        }
    }
}
