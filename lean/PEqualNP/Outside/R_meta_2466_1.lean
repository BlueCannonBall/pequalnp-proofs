import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2466_1
    (supportBound : ∀ n (C : Circuit), IsAO2 n C →
      ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧ ∀ x y : Fin n → Bool,
        (∀ i ∈ S, x i = y i) → circuitFun n C x = circuitFun n C y)
    (largePlane : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      67 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ x, circuitFun (N+N) C x = decide (∃ p l, I p l ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      IsReadK (N+N) C 2 →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false} ≤ 34*C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ x, circuitFun (N+N) C x = decide (∃ p l, I p l ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      IsReadK (N+N) C 2 →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false} ≤ 34*C.size := by
  intro q N I inst C hq hN hcols hpairs hao heval hread
  by_cases hlarge : 67 ≤ q
  · exact largePlane q N I C hlarge hN hcols hpairs hao heval hread
  obtain ⟨S, hsize, hsupport⟩ := supportBound _ C hao
  have endpoints (p l : Fin N) (hpl : I p l) :
      Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
    let x : Fin (N+N) → Bool := Fin.addCases (fun i => decide (i = p)) (fun i => decide (i = l))
    let y := fun i => x i && decide (i ∈ S)
    have hx : circuitFun (N+N) C x = true := by
      rw [heval, decide_eq_true_eq]
      exact ⟨p, l, hpl, by simp only [x, Fin.addCases_left, decide_true],
        by simp only [x, Fin.addCases_right, decide_true]⟩
    have hy := (hsupport x y (by intro i hi; simp [y, hi])).symm.trans hx
    rw [heval, decide_eq_true_eq] at hy
    obtain ⟨p', l', _, hp', hl'⟩ := hy
    simp only [y, x, Fin.addCases_left, Fin.addCases_right, Bool.and_eq_true,
      decide_eq_true_eq] at hp' hl'
    obtain ⟨rfl, hp⟩ := hp'
    obtain ⟨rfl, hl⟩ := hl'
    exact ⟨hp, hl⟩
  haveI : Nontrivial (Fin N) := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Fintype.card_fin]; omega)
  have hall : S = Finset.univ := by
    apply Finset.eq_univ_of_forall
    apply Fin.addCases
    · intro p
      obtain ⟨r, hr⟩ := exists_ne p
      obtain ⟨l, hpl, _⟩ := hpairs p r hr.symm
      exact (endpoints p l hpl.1).1
    · intro l
      have hpos : 0 < Fintype.card {p // I p l} := by rw [hcols]; omega
      obtain ⟨⟨p, hpl⟩⟩ := Fintype.card_pos_iff.mp hpos
      exact (endpoints p l hpl).2
  rw [hall, Finset.card_univ, Fintype.card_fin] at hsize
  let D := {e : Fin N × Fin N // I e.1 e.2 ∧
    lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
    lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false}
  let f (e : D) : (l : Fin N) × {p // I p l} := ⟨e.val.2, e.val.1, e.property.1⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : (l : Fin N) × {p // I p l} => z.2.val) hab)
      (congrArg Sigma.fst hab)
  have hcount := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sigma] at hcount
  simp only [hcols, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hcount
  apply hcount.trans
  by_cases hsmall : q ≤ 33
  · have h := Nat.mul_le_mul_left N (show q+1 ≤ 34 by omega)
    omega
  · have h := Nat.mul_le_mul_left N (show q+1 ≤ 67 by omega)
    omega
