plugins {
    id("org.gradle.toolchains.foojay-resolver-convention") version "0.5.0"
}
rootProject.name = "ArendProofSearch"

// Local Arend builds - uncomment if needed for development
includeBuild("../arend-lang-new/Arend")
//includeBuild("../arend-lang-new/Arend/base")
//includeBuild("../arend-lang-new/Arend/api")

