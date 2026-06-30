package typechecker.cli

import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.apache.commons.cli.ParseException
import search.best_first.BestFirstSearch
import typechecker.cli.proofstep.CliLLMStepGenerator
import java.nio.file.Paths

fun runCliSearch(args: Array<String>) {
    val cmdOptions = Options()
    cmdOptions.addOption(
        Option.builder("L").longOpt("libdir").hasArg().argName("dir")
            .desc("directory containing the library (with arend.yaml)").build()
    )
    cmdOptions.addOption(
        Option.builder("m").longOpt("module-def").hasArg().argName("MODULE:DEF")
            .desc("module and definition to search (e.g., testPS:myTheorem)").build()
    )
    cmdOptions.addOption(
        Option.builder().longOpt("model").hasArg().argName("model-id")
            .desc("LLM model ID (default: openai/gpt-4o)").build()
    )

    val cmdLine = try {
        DefaultParser().parse(cmdOptions, args)
    } catch (e: ParseException) {
        System.err.println(e.message)
        return
    }

    val libPath = cmdLine.getOptionValue("L")
        ?: run { System.err.println("Missing required option: -L <libdir>"); return }
    val moduleDef = cmdLine.getOptionValue("m")
        ?: run { System.err.println("Missing required option: --module-def MODULE:DEF"); return }
    val modelId = cmdLine.getOptionValue("model", "openai/gpt-4o")

    println("Connecting to Arend CLI for library at $libPath...")
    CliConnection(Paths.get(libPath)).use { cli ->
        println("Connected. Finding goals in $moduleDef...")
        val initialProof = PlainTextProof.initial(cli, moduleDef)
        val goals = initialProof.goals()

        if (goals.isEmpty()) {
            println("No goals found in $moduleDef")
            return
        }

        println("Found ${goals.size} goal(s):")
        for (goal in goals) {
            println("  $goal")
        }

        val generator = CliLLMStepGenerator(cli, moduleDef, modelId)
        val search = BestFirstSearch<PlainTextGoal>(generator)

        println("Starting proof search...")
        val result = search.search(initialProof)

        if (result != null) {
            println("\nFound proof!")
            println(result)
        } else {
            println("\nProof search exhausted without finding a proof.")
        }
    }
}
