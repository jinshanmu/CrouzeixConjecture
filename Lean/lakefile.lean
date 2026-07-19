import Lake

open Lake DSL

package «crouzeix-conjecture»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "8f9d9cff6bd728b17a24e163c9402775d9e6a365"

@[default_target]
lean_lib CrouzeixConjecture

@[default_script]
script verify do
  let child ← IO.Process.spawn {
    cmd := "sh"
    args := #["verify.sh"]
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  child.wait
