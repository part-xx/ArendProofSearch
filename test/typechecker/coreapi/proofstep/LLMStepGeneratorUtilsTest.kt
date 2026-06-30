package typechecker.coreapi.proofstep

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.test.assertTrue
import java.io.File

class LLMStepGeneratorUtilsTest {

    @Test
    fun `extractTermFromResponse extracts term between tags`() {
        val response = "Plan: We need to rewrite.\n[TERM]rewrite p idp[/TERM]"
        val term = LLMStepGenerator.extractTermFromResponse(response)
        assertEquals("rewrite p idp", term)
    }

    @Test
    fun `extractTermFromResponse handles multiline terms`() {
        val response = "[TERM]\\case \\elim i \\with {\n  | zero => {?}\n  | suc i' => {?}\n}[/TERM]"
        val term = LLMStepGenerator.extractTermFromResponse(response)
        assertEquals("\\case \\elim i \\with {\n  | zero => {?}\n  | suc i' => {?}\n}", term)
    }

    @Test
    fun `extractTermFromResponse returns null when no start tag`() {
        val response = "Just some text without tags"
        assertNull(LLMStepGenerator.extractTermFromResponse(response))
    }

    @Test
    fun `extractTermFromResponse returns null when no end tag`() {
        val response = "[TERM]rewrite p but no end tag"
        assertNull(LLMStepGenerator.extractTermFromResponse(response))
    }

    @Test
    fun `extractTermFromResponse trims whitespace`() {
        val response = "[TERM]  idp  [/TERM]"
        assertEquals("idp", LLMStepGenerator.extractTermFromResponse(response))
    }

    @Test
    fun `extractTermFromResponse handles empty term`() {
        val response = "[TERM][/TERM]"
        assertEquals("", LLMStepGenerator.extractTermFromResponse(response))
    }

    @Test
    fun `extractTermFromResponse uses first occurrence`() {
        val response = "[TERM]first[/TERM] some text [TERM]second[/TERM]"
        assertEquals("first", LLMStepGenerator.extractTermFromResponse(response))
    }

    @Test
    fun `extractTermFromResponse handles Arend backslash syntax`() {
        val response = "[TERM]\\lam x => x[/TERM]"
        assertEquals("\\lam x => x", LLMStepGenerator.extractTermFromResponse(response))
    }

    @Test
    fun `parseConcatenatedJson parses single object`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"key": "value", "num": 42}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(1, results.size)
            assertEquals("value", results[0]["key"])
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson parses multiple concatenated objects`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"a": 1}{"b": 2}{"c": 3}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(3, results.size)
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson handles nested braces`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"outer": {"inner": "value"}, "list": [1, 2]}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(1, results.size)
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson handles strings with braces`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"expr": "\\case {x} \\with { | zero => {?} }"}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(1, results.size)
            assertTrue((results[0]["expr"] as String).contains("\\case"))
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson handles escaped quotes in strings`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"text": "a \"quoted\" word"}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(1, results.size)
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson handles whitespace between objects`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"a": 1}
  {"b": 2}
{"c": 3}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(3, results.size)
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson handles arrays in values`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{"Context": ["x : Nat", "y : Nat"], "Expected type": "x = y"}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(1, results.size)
            val ctx = results[0]["Context"]
            assertTrue(ctx is List<*>)
            assertEquals(2, (ctx as List<*>).size)
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson returns empty list for empty file`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertTrue(results.isEmpty())
        } finally {
            tempFile.delete()
        }
    }

    @Test
    fun `parseConcatenatedJson parses actual examples file structure`() {
        val tempFile = File.createTempFile("test", ".json")
        try {
            tempFile.writeText("""{
    "Context": ["a : Nat", "b : Nat"],
    "Expected type": "a + b = b + a",
    "Expression": "rewrite (+-comm a b) idp",
    "Premises": ["\\func + (a b : Nat) : Nat"]
}{
    "Context": [],
    "Expected type": "0 = 0",
    "Expression": "idp",
    "Premises": []
}""")
            val results = LLMStepGenerator.parseConcatenatedJson(tempFile)
            assertEquals(2, results.size)
            assertEquals("a + b = b + a", results[0]["Expected type"])
            assertEquals("idp", results[1]["Expression"])
        } finally {
            tempFile.delete()
        }
    }
}
