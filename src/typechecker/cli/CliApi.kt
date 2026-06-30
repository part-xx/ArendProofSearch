package typechecker.cli

interface CliApi {
    fun findGoals(moduleDef: String): FindGoalsResponse
    fun checkExpression(moduleDef: String, goalId: String, expression: String): CheckResult
    fun applyStep(moduleDef: String, goalId: String, expression: String): ApplyStepResponse
    fun getScope(moduleDef: String, goalId: String): ScopeResponse
    fun proofSearch(pattern: String): ProofSearchResponse
}
