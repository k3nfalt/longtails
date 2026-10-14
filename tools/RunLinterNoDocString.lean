import Batteries.Tactic.Lint

open Lean Batteries.Tactic.Lint

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[`LongTails, `Batteries.Tactic.Lint] {}
    (trustLevel := 1024) (loadExts := true)
  let (failed, _) ← (do
    let decls ← getDeclsInPackage `LongTails
    let linters := (← getChecks (slow := true) (runOnly := none) (runAlways := none)).filter
      (·.name != `docBlame)
    let results ← lintCore decls linters (inIO := true) (currentModule := `LongTails)
    let report ← formatLinterResults results decls (groupByFilename := true)
      (useErrorFormat := true) "in LongTails" (runSlowLinters := true) .medium linters.size
    IO.print (← report.toString)
    pure (results.any (!·.2.isEmpty)) : CoreM Bool).toIO
      { fileName := "", fileMap := default } { env }
  IO.Process.exit (if failed then 1 else 0)
