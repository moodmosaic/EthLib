import Hedgehog

/-!
# A reference implementation in another process

EthLib's theorems say what its definitions guarantee, and they are stated about those definitions.
They cannot say that a definition is the function its source defines.
A reference implementation written apart from EthLib can, on the inputs it is given.

An oracle is a Python program under `oracle/` that reads one command per line and answers each with
one line.
The words of a line are separated by tabs, and bytes are in hexadecimal, `-` for none.
An answer that starts with `error` says the reference refused the input.

The interpreter is `.venv/bin/python` of this package, or the one `ETHLIB_ORACLE_PYTHON` names.
`oracle/requirements.txt` lists what it needs.
-/

open Hedgehog

namespace Support

/-- The oracle process: one command line in, one answer line out. -/
structure Oracle where
  stdin : IO.FS.Handle
  stdout : IO.FS.Handle

/-- Start `oracle/<name>.py`, from the directory of this package. -/
def Oracle.start (name : String) : IO Oracle := do
  let python := (← IO.getEnv "ETHLIB_ORACLE_PYTHON").getD ".venv/bin/python"
  let child ← IO.Process.spawn
    { cmd := python, args := #["-I", s!"oracle/{name}.py"],
      stdin := .piped, stdout := .piped, stderr := .inherit }
  pure ⟨child.stdin, child.stdout⟩

/-- Send a command and read its answer. -/
def Oracle.ask (oracle : Oracle) (words : List String) : TestT IO String := evalIO do
  oracle.stdin.putStrLn ("\t".intercalate words)
  oracle.stdin.flush
  let line ← oracle.stdout.getLine
  if line.isEmpty then throw (IO.userError "the oracle gave no answer")
  pure (String.ofList (line.toList.filter (· ≠ '\n')))

end Support
