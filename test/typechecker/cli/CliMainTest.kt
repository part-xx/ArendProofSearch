package typechecker.cli

import typechecker.cli.proofstep.CandidateGenerationMode
import typechecker.cli.proofstep.TacticPromptFormat
import java.nio.file.Files
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNull

class CliMainTest {
    @Test
    fun `backend parser accepts local and remote`() {
        assertEquals(LLMBackend.LOCAL, LLMBackend.parse("local"))
        assertEquals(LLMBackend.REMOTE, LLMBackend.parse("REMOTE"))
        assertNull(LLMBackend.parse("hosted"))
    }

    @Test
    fun `regime parser accepts fine tuned and instruction aliases`() {
        assertEquals(TacticPromptFormat.FINE_TUNED_AREND, parsePromptRegime("fine-tuned"))
        assertEquals(TacticPromptFormat.FINE_TUNED_AREND, parsePromptRegime("fine"))
        assertEquals(TacticPromptFormat.QWEN3_DIRECT_V1, parsePromptRegime("qwen3-direct-v1"))
        assertEquals(TacticPromptFormat.QWEN3_DIRECT_V1, parsePromptRegime("qwen3-direct"))
        assertEquals(TacticPromptFormat.QWEN3_DIRECT_V1, parsePromptRegime("direct-v1"))
        assertEquals(TacticPromptFormat.INSTRUCTION, parsePromptRegime("instruction"))
        assertEquals(TacticPromptFormat.INSTRUCTION, parsePromptRegime("general"))
        assertNull(parsePromptRegime("chat"))
    }

    @Test
    fun `backend defaults use instruction prompts`() {
        assertEquals(TacticPromptFormat.INSTRUCTION, defaultPromptRegime(LLMBackend.LOCAL))
        assertEquals(TacticPromptFormat.INSTRUCTION, defaultPromptRegime(LLMBackend.REMOTE))
    }

    @Test
    fun `qwen3 direct has a canonical name and defaults to batch candidates`() {
        assertEquals("qwen3-direct-v1", promptRegimeName(TacticPromptFormat.QWEN3_DIRECT_V1))
        assertEquals(
            CandidateGenerationMode.BATCH,
            defaultCandidateMode(TacticPromptFormat.QWEN3_DIRECT_V1)
        )
        assertEquals(
            CandidateGenerationMode.ITERATIVE_FEEDBACK,
            defaultCandidateMode(TacticPromptFormat.INSTRUCTION)
        )
    }

    @Test
    fun `candidate mode parser accepts iterative and batch aliases`() {
        assertEquals(CandidateGenerationMode.ITERATIVE_FEEDBACK, parseCandidateMode("iterative"))
        assertEquals(CandidateGenerationMode.ITERATIVE_FEEDBACK, parseCandidateMode("feedback"))
        assertEquals(CandidateGenerationMode.BATCH, parseCandidateMode("BATCH"))
        assertNull(parseCandidateMode("independent"))
    }

    @Test
    fun `premises loader preserves dataset declarations and ordering`() {
        val path = Files.createTempFile("arend-premises", ".json")
        try {
            Files.writeString(
                path,
                """{"Premises":["byRight B : A || B","\\func inv (p : a = b) : b = a\n  => {?hidden}"]}"""
            )

            assertEquals(
                listOf(
                    "byRight B : A || B",
                    "\\func inv (p : a = b) : b = a\n  => {?hidden}"
                ),
                loadPremises(path)
            )
        } finally {
            Files.deleteIfExists(path)
        }
    }

    @Test
    fun `premises loader accepts an explicit empty array and rejects non strings`() {
        val emptyPath = Files.createTempFile("arend-premises-empty", ".json")
        val invalidPath = Files.createTempFile("arend-premises-invalid", ".json")
        try {
            Files.writeString(emptyPath, "[]")
            Files.writeString(invalidPath, "[\"valid\", 42]")

            assertEquals(emptyList(), loadPremises(emptyPath))
            assertFailsWith<IllegalArgumentException> { loadPremises(invalidPath) }
        } finally {
            Files.deleteIfExists(emptyPath)
            Files.deleteIfExists(invalidPath)
        }
    }
}
