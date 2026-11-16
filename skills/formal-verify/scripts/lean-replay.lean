-- Copyright (c) 2026 Michael Denyer
-- SPDX-License-Identifier: GPL-3.0-only
-- Replay exact modules with the pin's checker, without its CLI's prefix search.
import LeanChecker

open Lean

unsafe def replayModules : IO Unit := do
  initSearchPath (← findSysroot)
  let some path ← IO.getEnv "AFV_REPLAY_MODULES"
    | throw <| IO.userError "AFV_REPLAY_MODULES must name a module list"
  for module in (← IO.FS.lines path) do
    IO.println s!"replaying {module}"
    try replayFromImports module.toName
    catch error =>
      IO.eprintln s!"leanchecker found a problem in {module}"
      throw error

#eval replayModules
