package typechecker.cli

import kotlinx.serialization.json.Json
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class CliResponsesTest {

    private val json = Json { ignoreUnknownKeys = true }

    @Test
    fun `FindGoalsResponse deserializes correctly`() {
        val raw = """
        {
          "definition": "testPS:myTheorem",
          "goals": [
            {
              "id": "0",
              "name": "",
              "expectedType": "a + b = b + a",
              "context": [
                {"name": "a", "type": "Nat"},
                {"name": "b", "type": "Nat"}
              ]
            }
          ]
        }
        """.trimIndent()

        val result = json.decodeFromString<FindGoalsResponse>(raw)
        assertEquals("testPS:myTheorem", result.definition)
        assertEquals(1, result.goals.size)
        assertEquals("0", result.goals[0].id)
        assertEquals("a + b = b + a", result.goals[0].expectedType)
        assertEquals(2, result.goals[0].context.size)
        assertEquals("a", result.goals[0].context[0].name)
        assertEquals("Nat", result.goals[0].context[0].type)
    }

    @Test
    fun `FindGoalsResponse handles empty goals`() {
        val raw = """{"definition": "M:D", "goals": []}"""
        val result = json.decodeFromString<FindGoalsResponse>(raw)
        assertTrue(result.goals.isEmpty())
    }

    @Test
    fun `GoalInfo defaults work`() {
        val raw = """{"id": "0", "expectedType": "Nat"}"""
        val result = json.decodeFromString<GoalInfo>(raw)
        assertEquals("", result.name)
        assertTrue(result.context.isEmpty())
    }

    @Test
    fun `ApplyStepResponse deserializes success with remaining goals`() {
        val raw = """
        {
          "success": true,
          "proof": "rewrite p {?}",
          "goals": [
            {"id": "0", "expectedType": "b = b", "context": []}
          ],
          "errors": []
        }
        """.trimIndent()

        val result = json.decodeFromString<ApplyStepResponse>(raw)
        assertTrue(result.success)
        assertEquals("rewrite p {?}", result.proof)
        assertEquals(1, result.goals.size)
        assertEquals("b = b", result.goals[0].expectedType)
    }

    @Test
    fun `ApplyStepResponse deserializes complete proof`() {
        val raw = """{"success": true, "proof": "idp", "goals": [], "errors": []}"""
        val result = json.decodeFromString<ApplyStepResponse>(raw)
        assertTrue(result.success)
        assertTrue(result.goals.isEmpty())
    }

    @Test
    fun `ScopeResponse deserializes correctly`() {
        val raw = """
        {
          "scope": [
            {"name": "Nat.+", "kind": "FUNC", "type": "Nat -> Nat -> Nat"},
            {"name": "idp", "kind": "CONSTRUCTOR", "type": "a = a"}
          ],
          "locals": [
            {"name": "x", "type": "Nat"}
          ]
        }
        """.trimIndent()

        val result = json.decodeFromString<ScopeResponse>(raw)
        assertEquals(2, result.scope.size)
        assertEquals("Nat.+", result.scope[0].name)
        assertEquals("FUNC", result.scope[0].kind)
        assertEquals(1, result.locals.size)
    }

    @Test
    fun `ScopeResponse defaults to empty lists`() {
        val raw = """{}"""
        val result = json.decodeFromString<ScopeResponse>(raw)
        assertTrue(result.scope.isEmpty())
        assertTrue(result.locals.isEmpty())
    }

    @Test
    fun `SearchResult deserializes correctly`() {
        val raw = """
        {
          "library": "arend-lib",
          "module": "Arith.Nat",
          "name": "+-comm",
          "kind": "\\lemma",
          "signature": "(a b : Nat) : a + b = b + a",
          "location": {"file": "src/Arith/Nat.ard", "line": 42, "col": 0}
        }
        """.trimIndent()

        val result = json.decodeFromString<SearchResult>(raw)
        assertEquals("arend-lib", result.library)
        assertEquals("Arith.Nat", result.module)
        assertEquals("+-comm", result.name)
        assertEquals("\\lemma", result.kind)
        assertNotNull(result.location)
        assertEquals(42, result.location!!.line)
    }

    @Test
    fun `SearchResult handles null location`() {
        val raw = """{"library": "lib", "module": "M", "name": "f", "kind": "\\func", "signature": "Nat"}"""
        val result = json.decodeFromString<SearchResult>(raw)
        assertEquals(null, result.location)
    }

    @Test
    fun `ProofSearchResponse deserializes correctly`() {
        val raw = """
        {
          "results": [
            {"library": "lib", "module": "M", "name": "f", "kind": "\\func", "signature": "Nat -> Nat"}
          ],
          "count": 1
        }
        """.trimIndent()

        val result = json.decodeFromString<ProofSearchResponse>(raw)
        assertEquals(1, result.count)
        assertEquals(1, result.results.size)
    }

    @Test
    fun `ProofSearchResponse defaults work`() {
        val raw = """{}"""
        val result = json.decodeFromString<ProofSearchResponse>(raw)
        assertTrue(result.results.isEmpty())
        assertEquals(0, result.count)
    }

    @Test
    fun `ContextBinding round-trips through serialization`() {
        val raw = """{"name": "myVar", "type": "Nat -> Bool"}"""
        val deserialized = json.decodeFromString<ContextBinding>(raw)
        assertEquals("myVar", deserialized.name)
        assertEquals("Nat -> Bool", deserialized.type)
    }

    @Test
    fun `ContextBinding handles complex types`() {
        val raw = """{"name": "f", "type": "\\Pi (x : Nat) -> x = 0 -> Bool"}"""
        val result = json.decodeFromString<ContextBinding>(raw)
        assertEquals("f", result.name)
        assertTrue(result.type.contains("\\Pi"))
    }

    private fun assertNotNull(value: Any?) {
        assertTrue(value != null, "Expected non-null value")
    }
}
