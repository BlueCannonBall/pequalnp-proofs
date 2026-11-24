import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2024_1
    (negateNine : ∀ (before after : List Gate) (out : ℕ),
      before.length + after.length ≤ 13 → (∀ g ∈ before, 9 ∉ g.inputs) →
      let C : Circuit := ⟨before ++ ⟨.not, [9]⟩ :: after, out⟩
      FanInTwo C → out ≤ 24 → out ≠ 9 → (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (negateOther : ∀ (before after : List Gate) (out k : ℕ),
      k ≠ 9 → before.length + after.length ≤ 13 → (∀ g ∈ before, 9 ∉ g.inputs) →
      let C : Circuit := ⟨before ++ ⟨.not, [k]⟩ :: after, out⟩
      FanInTwo C → out ≤ 24 → out ≠ 9 → (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) :
    ∀ (before after : List Gate) (pins : List ℕ) (out : ℕ),
      before.length + after.length ≤ 13 → (∀ g ∈ before, 9 ∉ g.inputs) → 9 ∈ pins →
      let C : Circuit := ⟨before ++ ⟨.not, pins⟩ :: after, out⟩
      FanInTwo C → out ≤ 24 → out ≠ 9 → (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5) := by
  intro before after pins out hsize hbefore hnine
  cases pins with
  | nil => simp at hnine
  | cons k rest =>
    intro C hfan hout hne hbound
    let D : Circuit := ⟨before ++ ⟨.not, [k]⟩ :: after, out⟩
    have horig : (⟨.not, k :: rest⟩ : Gate) ∈ C.gates := by simp [C]
    have unchanged (g : Gate) (hg : g ∈ before ∨ g ∈ after) : g ∈ C.gates := by
      exact List.mem_append.mpr (hg.imp_right (List.mem_cons_of_mem _))
    have fan : FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hfan g (unchanged g (.inl h))
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨(hfan _ horig).1, by change 1 ≤ 2; decide⟩
      · exact hfan g (unchanged g (.inr h))
    have bounds : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24 := by
      intro g hg i hi
      rcases List.mem_append.mp hg with h | h
      · exact hbound g (unchanged g (.inl h)) i hi
      rcases List.mem_cons.mp h with rfl | h
      · have hik : i = k := List.mem_singleton.mp hi
        exact hik ▸ hbound _ horig k (List.mem_cons_self ..)
      · exact hbound g (unchanged g (.inr h)) i hi
    have same (bits : List Bool) : C.eval bits = D.eval bits := by
      simp only [Circuit.eval, Circuit.wires, C, D, List.foldl_append, List.foldl_cons]
      rfl
    simp_rw [same]
    by_cases hk : k = 9
    · subst k
      exact negateNine before after out hsize hbefore fan hout hne bounds
    · exact negateOther before after out k hk hsize hbefore fan hout hne bounds
