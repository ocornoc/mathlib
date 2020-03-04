import tactic.lint

def c : ℕ := default _
def d : ℕ := default _

class foo (α : Type)
-- type class resolution for [foo α] will always time out
instance foo.foo {α} [foo α] : foo α := ‹foo α›

-- breaks simp on any term containing c
@[simp] lemma c_eq_d [foo ℕ] : c = d := by refl

example : c = d + 0 :=
begin
  success_if_fail { simp },
  refl
end

-- This lemma can never result in a successful simplification, because simp will
-- fail after processing the right-hand side.
@[simp] lemma d_add_d : d + d = c := by refl

open tactic
#eval do
decl ← get_decl ``d_add_d,
res ← linter.simp_nf.test decl,
trace res,
-- linter complains
guard res.is_some
