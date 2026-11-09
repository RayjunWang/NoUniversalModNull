/- Tooling only: Lean itself supplies import spans and the final module scope depth.
No declaration is split, renamed, or removed by the bundle generator. -/
import Lean

open Lean Elab Parser

unsafe def main (args : List String) : IO UInt32 := do
  let headerOnly := args.head? == some "--header-only"
  let files := if headerOnly then args.drop 1 else args
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  for fileName in files do
    let input ← IO.FS.readFile fileName
    let inputCtx := Parser.mkInputContext input fileName
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    if messages.hasErrors then
      IO.eprintln s!"Unable to parse module header: {fileName}"
      return 1
    let mut spans : Array Json := #[]
    if let `(Parser.Module.header| $[module%$moduleTk]? $[prelude%$preludeTk]? $importsStx*) := header then
      if moduleTk.isSome || preludeTk.isSome then
        IO.eprintln s!"Module/prelude directives require a separate bundle strategy: {fileName}"
        return 1
      for stx in importsStx do
        let some start := stx.raw.getPos? | return 1
        let some stop := stx.raw.getTailPos? | return 1
        spans := spans.push <| Json.mkObj [
          ("start",toJson start.byteIdx),("stop",toJson stop.byteIdx)]
    let imports := HeaderSyntax.imports header false |>.map (fun i => Json.str i.module.toString)
    let mut depth : Nat := 0
    unless headerOnly do
      let (env, messages) ← processHeader header {} messages inputCtx
      let s ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
      if s.commandState.messages.hasErrors then
        for msg in s.commandState.messages.toList do
          IO.eprintln (← msg.toString)
        return 1
      depth := s.commandState.scopes.length
    IO.println (Json.mkObj [
      ("file",Json.str fileName),("imports",Json.arr imports),
      ("import_spans",Json.arr spans),("scope_depth",toJson depth)]).compress
  return 0
