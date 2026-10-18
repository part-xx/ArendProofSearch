package typechecker.cli

import typechecker.cli.proofstep.CandidateGenerationMode
import typechecker.cli.proofstep.CliLLMStepGenerator
import typechecker.cli.proofstep.TacticPromptFormat
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class Qwen3DirectPromptTest {
    @Test
    fun `direct v1 prompt exactly matches the versioned training contract`() {
        val prompt = CliLLMStepGenerator.qwen3DirectV1Prompt(
            context = listOf("x : Nat", "p : x = 0"),
            expectedType = "0 = x",
            premises = listOf(
                "\\func inv (p : a = b) : b = a\n  => {?hidden_proof}",
                "\\lemma helper : P\n  => {?hidden_proof}"
            )
        )

        assertEquals(
            """<CONTEXT>
x : Nat
p : x = 0
</CONTEXT>
<GOAL>
0 = x
</GOAL>
<PREMISES>
\func inv (p : a = b) : b = a
  => {?hidden_proof}

\lemma helper : P
  => {?hidden_proof}
</PREMISES>""",
            prompt
        )
        assertEquals(
            "Generate one Arend proof step. Return one tagged tactic only.",
            CliLLMStepGenerator.QWEN3_DIRECT_V1_SYSTEM_MESSAGE
        )
    }

    @Test
    fun `direct v1 prompt preserves explicit empty sections`() {
        assertEquals(
            """<CONTEXT>

</CONTEXT>
<GOAL>
Nat
</GOAL>
<PREMISES>

</PREMISES>""",
            CliLLMStepGenerator.qwen3DirectV1Prompt(emptyList(), "Nat", emptyList())
        )
    }

    @Test
    fun `direct v1 only accepts one complete tactic block`() {
        val generator = CliLLMStepGenerator(
            FakeCli(),
            "M:D",
            promptFormat = TacticPromptFormat.QWEN3_DIRECT_V1,
            llmClient = ScriptedBatchLLMClient(emptyList())
        )

        assertNotNull(generator.parseQwen3DirectStepFromResponse("[REFINE]idp[/REFINE]"))
        assertNotNull(generator.parseQwen3DirectStepFromResponse("\n[INTRO]\n[/INTRO]\n"))
        assertNotNull(generator.parseQwen3DirectStepFromResponse("[APPLY idp]\n[/APPLY]"))
        assertNull(generator.parseQwen3DirectStepFromResponse("[REFINE]\n[/REFINE]"))
        assertNull(generator.parseQwen3DirectStepFromResponse("plan first\n[REFINE]idp[/REFINE]"))
        assertNull(
            generator.parseQwen3DirectStepFromResponse(
                "[REFINE]idp[/REFINE]\n[REFINE]other[/REFINE]"
            )
        )
    }

    @Test
    fun `direct v1 rejects iterative feedback mode`() {
        val error = assertFailsWith<IllegalArgumentException> {
            CliLLMStepGenerator(
                FakeCli(),
                "M:D",
                candidateGenerationMode = CandidateGenerationMode.ITERATIVE_FEEDBACK,
                promptFormat = TacticPromptFormat.QWEN3_DIRECT_V1,
                llmClient = ScriptedLLMClient(emptyList())
            )
        }

        assertTrue(error.message.orEmpty().contains("direct examples only"))
    }

    @Test
    fun `direct v1 native completion count spends the raw proposal budget`() {
        assertEquals(
            10,
            CliLLMStepGenerator.batchCompletionCount(
                TacticPromptFormat.QWEN3_DIRECT_V1,
                maxAttempts = 10,
                maxCandidates = 2
            )
        )
    }
}
