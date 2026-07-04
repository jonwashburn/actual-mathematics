import ActualMathematics.DeltaSpine.GoldenInt

namespace ActualMathematics.PRCGrow.EightTickSpinor

-- (1) The 8-tick clock

def tick : Fin 8 → Fin 8 := fun t => t + 1

theorem eight_tick_period : tick^[8] = id := by
  funext x
  have h : ∀ y : Fin 8, tick^[8] y = y := by decide
  exact h x

theorem eight_tick_minimal : ∀ n : Nat, 0 < n → n < 8 → tick^[n] 0 ≠ 0 := by
  intro n hn_pos hn_lt
  have h_cases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

-- (2) The spinor double cover

def tick16 : Fin 16 → Fin 16 := fun t => t + 1

def proj : Fin 16 → Fin 8 := fun t => ⟨t.val % 8, by have h := t.2; omega⟩

theorem proj_intertwine (t : Fin 16) : proj (tick16 t) = tick (proj t) := by
  apply Fin.ext
  show (t.val + 1) % 16 % 8 = (t.val % 8 + 1) % 8
  have h := t.2
  omega

theorem tick16_eight_not_closed : tick16^[8] 0 ≠ 0 := by decide

theorem tick16_sixteen_period : tick16^[16] = id := by
  funext x
  have h : ∀ y : Fin 16, tick16^[16] y = y := by decide
  exact h x

-- (3) The dimension pin

theorem dim_three (D : Nat) : 2^D = 8 ↔ D = 3 := by
  constructor
  · intro h
    by_cases hD : D < 4
    · have : D = 0 ∨ D = 1 ∨ D = 2 ∨ D = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · rfl
    · exfalso
      have heq : D = 4 + (D - 4) := by omega
      rw [heq, Nat.pow_add] at h
      have h2pow4 : (2^4 : ℕ) = 16 := rfl
      rw [h2pow4] at h
      have hge1 : 1 ≤ 2^(D-4) := by
        set k := D - 4
        clear h
        induction k with
        | zero => decide
        | succ j ih =>
          rw [Nat.pow_succ]
          omega
      omega
  · intro h
    rw [h]
    decide

end ActualMathematics.PRCGrow.EightTickSpinor
