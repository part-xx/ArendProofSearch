package typechecker.coreapi.proofstep

import typechecker.coreapi.ArendGoal
import typechecker.coreapi.proofstep.TestAppModule.assertProves
import typechecker.coreapi.proofstep.TestAppModule.module
import typechecker.coreapi.proofstep.TestAppModule.premises
import typechecker.coreapi.proofstep.TestAppModule.search
import kotlin.test.Test
import kotlin.test.assertNull

class AppGeneratorTest {

  private fun appGenerator(vararg premiseNames: String): (ArendGoal) -> AppGenerator {
    val premises = premises(*premiseNames)
    return { AppGenerator(premises, module.location) }
  }

  @Test
  fun `single application closes the goal`() {
    assertProves(search("app-one", appGenerator("q-lem", "p-lem")), "p-lem")
  }

  @Test
  fun `application whose argument becomes a subgoal`() {
    assertProves(search("app-two", appGenerator("q-lem", "p-lem")), "q-lem p-lem")
  }

  @Test
  fun `application with two subgoals`() {
    assertProves(search("app-branching", appGenerator("r-lem", "q-lem", "p-lem")), "r-lem p-lem (q-lem p-lem)")
  }

  @Test
  fun `implicit arguments are inferred from the goal across several steps`() {
    assertProves(search("app-implicit", appGenerator("pos-succ", "pos-one")), "pos-succ (pos-succ pos-one)")
  }

  @Test
  fun `explicit data arguments in one telescope are inferred and proof arguments become subgoals`() {
    assertProves(
      search("app-telescope", appGenerator("pos-pair", "pos-succ", "pos-one")),
      "pos-pair _ _ pos-one (pos-succ pos-one)"
    )
  }

  @Test
  fun `premise is used unapplied when the goal is a function type`() {
    assertProves(search("app-pi", appGenerator("q-lem", "p-lem")), "q-lem")
  }

  @Test
  fun `search fails when no premise applies`() {
    assertNull(search("app-unprovable", appGenerator("pos-succ", "pos-one")).proof)
  }
}
