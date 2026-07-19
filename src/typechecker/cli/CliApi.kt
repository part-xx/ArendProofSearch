package typechecker.cli

interface CliApi {
    fun findGoals(moduleDef: String): FindGoalsResponse
    fun applyStep(moduleDef: String, fullBody: String): ApplyStepResponse
    fun getScope(moduleDef: String, goalId: String): ScopeResponse
    fun proofSearch(pattern: String): ProofSearchResponse
    fun signature(moduleDef: String): String
    fun signatureInfo(moduleDef: String, name: String): SignatureInfoResponse?
    fun typeExpr(moduleDef: String, goalId: String, expression: String): TypeExprResponse?
}
