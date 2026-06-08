import Lean

def main (args : List String) : IO UInt32 := do
  let output ← IO.Process.output {
    cmd := "scripts/render-docs-site.sh"
    args := args.toArray
  }
  IO.print output.stdout
  IO.eprint output.stderr
  pure output.exitCode
