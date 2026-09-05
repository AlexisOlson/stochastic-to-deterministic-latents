import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"28e7de6320a34b5dba6452899319bec59d92afa1"
require stochastic_to_deterministic_latents from ".."
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"222c58dad7706a6e7cae46c0edd65ea881d3ee27"
require plausible from git "https://github.com/leanprover-community/plausible"@"123d15766ba49356c02ebad2a4462dfe12d79899"

package StochasticToDeterministicLatentsBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib StochasticToDeterministicLatentsBlueprint where
  roots := #[`StochasticToDeterministicLatentsBlueprint]
  globs := #[.one `StochasticToDeterministicLatentsBlueprint, .one `Blueprint,
    .submodules `Chapters]
