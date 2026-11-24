import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.HeptadCover
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2588_31
    (extendNegative : ∀ A B : Finset (Fin 13), A.card ≤ 2 → B.card ≤ 2 →
      (∀ p ∈ A, ∀ l ∈ B, p ∉ singerLines3 l) →
      ∃ Q ∈ quadrangles singerLines3, A ⊆ Q ∧ B ⊆ missLines singerLines3 Q)
    (boxBound :
      let input := fun (A B : Finset (Fin 13)) =>
        (List.ofFn fun i => decide (i ∈ A)) ++ List.ofFn fun i => decide (i ∈ B)
      let neg := fun Q => input Q (missLines singerLines3 Q)
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ andPairs 26 C →
        (∀ A B, A.card ≤ 2 → B.card ≤ 2 →
          C.eval (input A B) = decide (∃ p ∈ A, ∃ l ∈ B, p ∈ singerLines3 l)) →
        (∀ Q ∈ quadrangles singerLines3, C.eval (neg Q) = false) →
        (∀ j < C.size, (gateAt C j).op = .and → ∀ a ∈ (gateAt C j).inputs,
          ∃ Q ∈ quadrangles singerLines3,
            (C.wires (neg Q)).getD (26+j) false ≠ (C.wires (neg Q)).getD a false) →
        64 ≤ C.size) :
    let neg := fun (Q : Finset (Fin 13)) =>
      (List.ofFn fun i => decide (i ∈ Q)) ++ List.ofFn fun i => decide (i ∈ missLines singerLines3 Q)
    ∀ C : Circuit, IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      2 ≤ andPairs 26 C →
      (∀ p l : Fin 13, p ∈ singerLines3 l →
        C.eval ((List.ofFn fun i => decide (i = p)) ++ List.ofFn fun i => decide (i = l)) = true) →
      (∀ Q ∈ quadrangles singerLines3, C.eval (neg Q) = false) →
      (∀ j < C.size, (gateAt C j).op = .and → ∀ a ∈ (gateAt C j).inputs,
        ∃ Q ∈ quadrangles singerLines3,
          (C.wires (neg Q)).getD (26+j) false ≠ (C.wires (neg Q)).getD a false) →
      64 ≤ C.size := by
  intro neg C hao distinct nested edges rejects separated
  have readLe {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) (i : ℕ) :
      u.getD i false ≤ v.getD i false := by
    induction h generalizing i with
    | nil => simp
    | cons hab _ ih =>
      cases i with
      | zero => exact hab
      | succ i => exact ih i
  have mono : Monotone (fun x : Fin 26 → Bool => C.eval (List.ofFn x)) := by
    intro x y hxy
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have foldLe (gs : List Gate) (hg : ∀ g ∈ gs, g ∈ C.gates) (u v : List Bool)
        (h : List.Forall₂ (· ≤ ·) u v) :
        List.Forall₂ (· ≤ ·) (gs.foldl step u) (gs.foldl step v) := by
      induction gs generalizing u v with
      | nil => exact h
      | cons g gs ih =>
        apply ih (fun e he => hg e (by simp [he]))
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hao.2.2 g (hg g (by simp)))
        apply List.rel_append h
        apply List.Forall₂.cons _ List.Forall₂.nil
        have ha := readLe h a
        have hb := readLe h b
        rcases hao.1 g (hg g (by simp)) with hand | hor
        · rw [hand, hab]
          change GateOp.and.eval [u.getD a false, u.getD b false] ≤
            GateOp.and.eval [v.getD a false, v.getD b false]
          revert ha hb
          generalize u.getD a false = ua, v.getD a false = va,
            u.getD b false = ub, v.getD b false = vb
          decide +revert
        · rw [hor, hab]
          change GateOp.or.eval [u.getD a false, u.getD b false] ≤
            GateOp.or.eval [v.getD a false, v.getD b false]
          revert ha hb
          generalize u.getD a false = ua, v.getD a false = va,
            u.getD b false = ub, v.getD b false = vb
          decide +revert
    apply readLe (foldLe C.gates (fun _ h => h) _ _ _) C.output
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact hxy ⟨i, by simpa only [List.length_ofFn] using hi⟩
  apply boxBound C hao distinct nested _ rejects separated
  intro A B hA hB
  let row (S : Finset (Fin 13)) := fun i : Fin 13 => decide (i ∈ S)
  let X (P L : Finset (Fin 13)) := (List.ofFn (row P)) ++ List.ofFn (row L)
  have grow {P L P' L' : Finset (Fin 13)} (hp : P ⊆ P') (hl : L ⊆ L') :
      C.eval (X P L) ≤ C.eval (X P' L') := by
    have leRows {U V : Finset (Fin 13)} (h : U ⊆ V) (i : Fin 13) : row U i ≤ row V i := by
      by_cases hi : i ∈ U
      · simp [row, hi, h hi]
      · simp [row, hi]
    have hle : (Fin.addCases (row P) (row L) : Fin (13+13) → Bool) ≤
        Fin.addCases (row P') (row L') := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.addCases_left] using leRows hp j
      · simpa only [Fin.addCases_right] using leRows hl j
    have h := mono hle
    change C.eval (List.ofFn (Fin.append (row P) (row L))) ≤
      C.eval (List.ofFn (Fin.append (row P') (row L'))) at h
    simpa only [List.ofFn_fin_append] using h
  change C.eval (X A B) = _
  by_cases h : ∃ p ∈ A, ∃ l ∈ B, p ∈ singerLines3 l
  · simp only [h, decide_true]
    obtain ⟨p, hp, l, hl, he⟩ := h
    have one : C.eval (X {p} {l}) = true := by simpa [X, row] using edges p l he
    have le := grow (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
    rw [one] at le
    exact le_antisymm (by simp) le
  · have clear : ∀ p ∈ A, ∀ l ∈ B, p ∉ singerLines3 l := by
      intro p hp l hl he
      exact h ⟨p,hp,l,hl,he⟩
    obtain ⟨Q, hQ, hp, hl⟩ := extendNegative A B hA hB clear
    have le := grow hp hl
    have hn : C.eval (X Q (missLines singerLines3 Q)) = false := rejects Q hQ
    rw [hn] at le
    simp only [h, decide_false]
    exact le_antisymm le (by simp)
