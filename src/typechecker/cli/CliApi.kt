package typechecker.cli

interface CliApi {
    fun findGoals(moduleDef: String): FindGoalsResponse
    fun applyStep(moduleDef: String, fullBody: String): ApplyStepResponse
    fun getScope(moduleDef: String, goalId: String): ScopeResponse
    fun proofSearch(pattern: String): ProofSearchResponse
    fun signature(moduleDef: String): String
    fun signatureInfo(moduleDef: String, name: String): SignatureInfoResponse?
    /**
     * Infer the type of [expression] in the context of goal [goalId].
     * When [proofBody] (the current full proof body) is given, goal indices and
     * goal contexts are taken from that body instead of the on-disk one.
     */
    fun typeExpr(moduleDef: String, goalId: String, expression: String, proofBody: String? = null): TypeExprResponse?
}
