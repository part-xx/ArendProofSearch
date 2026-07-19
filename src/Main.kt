import com.openai.models.ChatModel
import org.apache.commons.cli.CommandLine
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.apache.commons.cli.ParseException
import org.arend.error.DummyErrorReporter
import org.arend.ext.error.ListErrorReporter
import org.arend.ext.module.FullName
import org.arend.ext.module.ModuleLocation
import org.arend.frontend.library.CliServerRequester
import org.arend.frontend.library.FileSourceLibrary
import org.arend.frontend.library.LibraryManager
import org.arend.frontend.library.SourceLibrary
import org.arend.frontend.source.PreludeResourceSource
import org.arend.prelude.Prelude
import org.arend.server.ArendServer
import org.arend.server.ProgressReporter
import org.arend.server.impl.ArendServerImpl
import org.arend.term.concrete.Concrete
import org.arend.term.group.ConcreteGroup
import org.arend.typechecking.computation.UnstoppableCancellationIndicator
import org.arend.core.expr.Expression
import org.arend.typechecking.result.TypecheckingResult
import org.arend.typechecking.visitor.CheckTypeVisitor
import org.arend.util.FileUtils
import org.arend.util.FileUtils.modulePath
// LLM dependencies - commented out for build
// Uncomment later to use JetBrains/koog or other LLM backend
//import org.jetbrains.ai.kotlin.playbook.getChatCompletionMessage
//import org.jetbrains.ai.kotlin.playbook.listModels
import search.best_first.BestFirstSearch
import typechecker.Proof
import typechecker.coreapi.ArendGoal
import typechecker.coreapi.ArendProof
import typechecker.coreapi.proofstep.LLMStepGenerator
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Objects
import java.util.function.Supplier

private fun parseArgs(args: Array<String>): CommandLine? {
  try {
    val cmdOptions = Options()
    cmdOptions.addOption(
      Option.builder("L").longOpt("libdir").hasArg().argName("dir").desc("directory containing libraries").build()
    )
    return DefaultParser().parse(cmdOptions, args)
  } catch (e: ParseException) {
    System.err.println(e.message)
    return null
  }
}

fun runSearch(args: Array<String>) {
  try {
    val cmdLine: CommandLine = parseArgs(args) ?: throw IllegalArgumentException("Missing required argument: -L <libdir>")
    val libDir: Path = Paths.get(cmdLine.getOptionValues("L")[0])
    val testFilename = "testPS"
    val errorReporter = ListErrorReporter()
    val libraryManager = LibraryManager(errorReporter)
    val server: ArendServer = ArendServerImpl(CliServerRequester(libraryManager), false, false, true)
    server.addReadOnlyModule(
      Prelude.MODULE_LOCATION,
      Supplier { Objects.requireNonNull<ConcreteGroup?>(PreludeResourceSource().loadGroup(DummyErrorReporter.INSTANCE)) })
    server.addErrorReporter(errorReporter)
    val library: SourceLibrary =
      FileSourceLibrary.fromConfigFile(libDir.resolve(FileUtils.LIBRARY_CONFIG_FILE), false, ListErrorReporter())
    libraryManager.updateLibrary(library, server)
    fun loadDependencies(lib: SourceLibrary) {
      for (dependencyName in lib.libraryDependencies) {
        if (libraryManager.containsLibrary(dependencyName)) continue
        val depConfigFile = libDir.resolve(dependencyName).resolve(FileUtils.LIBRARY_CONFIG_FILE)
        if (java.nio.file.Files.exists(depConfigFile)) {
          val depLibrary = FileSourceLibrary.fromConfigFile(depConfigFile, false, ListErrorReporter())
          if (depLibrary != null) {
            libraryManager.updateLibrary(depLibrary, server)
            for (mod in depLibrary.findModules(false)) {
              depLibrary.getSource(mod, false)?.load(server, errorReporter)
            }
            loadDependencies(depLibrary)
          }
        }
      }
    }
    loadDependencies(library)
    val modulePath = modulePath(testFilename)
    for (mod in library.findModules(false)) {
      if (mod != modulePath) {
        library.getSource(mod, false)?.load(server, errorReporter)
      }
    }
    val module = ModuleLocation(
      library.libraryName,
      ModuleLocation.LocationKind.SOURCE,
      modulePath
    )
    val checker = server.getCheckerFor(
      listOf(module)
    )
    library.getSource(modulePath, false)?.load(server, errorReporter)
    val group: ConcreteGroup = server.getRawGroup(module) ?: throw IllegalArgumentException("Module not found: $modulePath")
    checker.resolveAll(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
    val allModules = server.modules.toList()
    if (allModules.isNotEmpty()) {
      val allChecker = server.getCheckerFor(allModules)
      allChecker.typecheck(UnstoppableCancellationIndicator.INSTANCE, ProgressReporter.empty())
    }
    group.traverseGroup { x ->
      x.definition?.let {
        if (it is Concrete.FunctionDefinition) {
          checker.typecheck(
            FullName(module, it.data.refLongName),
            {
                errorReporter,
                pool,
                arendExtension,
                listener ->
              object : CheckTypeVisitor(errorReporter, pool, arendExtension, listener) {
                override fun visitGoal(expr: Concrete.GoalExpression, expectedType: Expression): TypecheckingResult {
                  val bestFirstSearch = BestFirstSearch<ArendGoal>(LLMStepGenerator(checker, server, library.libraryName, modulePath))
                  val goal = ArendGoal(expectedType, this, expr)
                  val initialProof = object : Proof<ArendGoal> {
                    override fun goals(): List<ArendGoal> = listOf(goal)
                    override fun replaceGoal(goal: ArendGoal, proof: Proof<ArendGoal>): Proof<ArendGoal>? = proof
                  }
                  val proof = bestFirstSearch.search(initialProof) as? ArendProof
                  if (proof != null) {
                    println("Found proof: " + proof.getProof())
                  }
                  return super.visitGoal(expr, expectedType)
                }
              }
            },
            null, errorReporter, UnstoppableCancellationIndicator.INSTANCE,
            ProgressReporter.empty()
          )
        }
      }
    }
  } catch (e: Exception) {
    e.printStackTrace()
  }
}

fun testLLM() {
  // LLM dependencies - commented out for build
  // Uncomment later to use JetBrains/koog or other LLM backend
  //println(
  //  "OpenAI chat completion:\n${
  //    getChatCompletionMessage(
  //      ChatModel.of("openai/gpt-4o-mini"),
  //      "Tell me what model are you?",
  //      instrument = false
  //    )
  //  }\n"
  //)
  //
  //println(
  //  "Available models:\n${
  //    listModels().joinToString("\n")
  //  }\n"
  //)
}

fun main(args: Array<String>) {
  testLLM()
  /*if (args.any { it == "--cli-mode" }) {
    val filteredArgs = args.filter { it != "--cli-mode" }.toTypedArray()
    typechecker.cli.runCliSearch(filteredArgs)
  } else {
    runSearch(args)
  }*/
}
