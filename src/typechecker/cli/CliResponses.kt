package typechecker.cli

import kotlinx.serialization.Serializable

@Serializable
data class ContextBinding(val name: String, val type: String)

@Serializable
data class GoalInfo(
    val id: String,
    val name: String = "",
    val expectedType: String,
    val context: List<ContextBinding> = emptyList()
)

@Serializable
data class FindGoalsResponse(
    val definition: String,
    val goals: List<GoalInfo>
)

@Serializable
data class ApplyStepResponse(
    val success: Boolean,
    val proof: String = "",
    val goals: List<GoalInfo> = emptyList(),
    val errors: List<String> = emptyList()
)

@Serializable
data class ScopeEntry(
    val name: String,
    val kind: String = "",
    val type: String = "",
    val module: String = ""
)

@Serializable
data class ScopeResponse(
    val scope: List<ScopeEntry> = emptyList(),
    val locals: List<ScopeEntry> = emptyList()
)

@Serializable
data class SearchResult(
    val library: String,
    val module: String,
    val name: String,
    val kind: String,
    val signature: String,
    val location: SearchLocation? = null
)

@Serializable
data class SearchLocation(
    val file: String? = null,
    val line: Int = 0,
    val col: Int = 0
)

@Serializable
data class ProofSearchResponse(
    val results: List<SearchResult> = emptyList(),
    val count: Int = 0
)

@Serializable
data class ParamInfo(
    val name: String,
    val type: String,
    val explicit: Boolean,
    val propositional: Boolean
)

@Serializable
data class TypeExprResponse(
    val type: String? = null
)

@Serializable
data class ConstructorInfo(
    val name: String,
    val params: List<ConstructorParam> = emptyList()
)

@Serializable
data class ConstructorParam(
    val name: String,
    val type: String,
    val explicit: Boolean
)

@Serializable
data class SignatureInfoResponse(
    val name: String,
    val params: List<ParamInfo> = emptyList(),
    val resultType: String? = null,
    val constructors: List<ConstructorInfo>? = null
)
