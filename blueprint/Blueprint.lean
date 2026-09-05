import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Chapters.Foundations
import Chapters.Pricing
import Chapters.NormalForm
import Chapters.Phases
import Chapters.Boundary
import Chapters.Recovery
import Chapters.Open

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Binary factor nine: dependency blueprint" =>

This graph links the definitions and dependency steps of the public binary factor-nine proof to their compiled Lean declarations. The [claim ledger](https://github.com/AlexisOlson/stochastic-to-deterministic-latents/blob/main/docs/claims.md) is authoritative for evidence tiers; this site records a checked projection of it.

{include 0 Chapters.Foundations}

{include 0 Chapters.Pricing}

{include 0 Chapters.NormalForm}

{include 0 Chapters.Phases}

{include 0 Chapters.Boundary}

{include 0 Chapters.Recovery}

{include 0 Chapters.Open}

{blueprint_graph (direction := LR)}
{blueprint_summary}
