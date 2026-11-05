import YM.Next.MULTISOURCE.Tome

/-! Actual compatible jets, at the common period-dependent prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice MeasureTheory Marker Finset Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {H : History G} {j p N : ℕ} {o : V → Site (H.S.side j p)} {D : Hot R → Pulse G (H.S.side (j+1) p)} {L : V→Pulse G (H.S.side j p)}
    {Z Z' : Hot (parts R) → Pulse G (H.S.side j p)} {F : Pulse G (H.S.side j p)}
variable {a b θ : ℝ}

omit [Fintype V] in
lemma Passage.more_b {i : Hot (parts R)} (h : Passage H j p N o D L Z i θ a F) (he : a≤b)
    (hx : ∀ i' : Hot (parts R), i'.sites ⊂ i.sites → Z i'=Z' i') : Passage H j p N o D L Z' i θ b F := by
  obtain ⟨t,Ht,hT⟩ := h.derivative
  refine ⟨h.records,h.budgeted.expand he,⟨t,Ht.expand he,hT⟩,?_⟩
  rw [h.exactF]; unfold defect; rw [proper_inputs _ Z Z' i hx]

lemma descend (H : History G) (R : Census V) (j p N : ℕ) (h : H.Selected) (he : j < N)
    (hθ : 0 ≤ θ) (ht : ∀ (d : Directions G (H.S.side j p)) i,(H.rep N p j).p.dirBound i d → ‖d‖ ≤ θ)
    (ℓ : ℝ) (m : ℕ) : ∃ b : ℝ, 0 ≤ b ∧
      ∀ (o : V → Site (H.S.side j p)) (D : Hot R → Pulse G _) (L : V → Pulse G _), Specified H j p N o D L ℓ →
      ∃ Z, ∀ i : Hot (parts R), i.sites.card ≤ m → Passage H j p N o D L Z i θ b (Z i) := by
  induction m with
  | zero => refine ⟨0,le_rfl,fun o D L _ => ⟨0,fun i hi => False.elim ((card_pos.mpr i.property).not_ge hi)⟩⟩
  | succ m hm =>
    obtain ⟨b,hb,Hb⟩ := hm
    choose f hf using fun z : Hot (parts R) => pass_ceiling H j p N h he hθ ht ℓ z hb
    let C := b + ∑ i, |f i|
    have hc : b≤C := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    refine ⟨C,hb.trans hc,fun o D L hL => ?_⟩
    obtain ⟨Z,hZ⟩ := Hb o D L hL
    have paid (i : Hot (parts R)) (hi : i.sites.card ≤ m+1) := hf i o D L hL Z (fun i' he => hZ i' (power_set R i m hi i' he))
    let D' i := if i.sites.card ≤ m then Z i else
      if h : i.sites.card≤m+1 then (paid i h).choose else 0
    have hD (i) (he : i.sites.card ≤ m) : Z i=D' i := (if_pos he).symm
    refine ⟨D',fun i hi => ?_⟩
    by_cases hh : i.sites.card ≤ m
    · rw [← hD i hh]
      exact (hZ i hh).more_b hc fun j hj => hD j (power_set R i m hi j hj)
    have hG : D' i = (paid i hi).choose := by simp only [D', hh,hi,↓reduceDIte,↓reduceIte]
    rw [hG]
    exact (paid i hi).choose_spec.more_b ((le_abs_self _).trans ((single_le_sum (fun j _ =>
      abs_nonneg (f j)) (mem_univ i)).trans (le_add_of_nonneg_left hb))) (fun y hy => hD y (power_set R i m hi y hy))

lemma transfer (H : History G) (R : Census V) (j p N : ℕ) (h : H.Selected) (he : j<N) (ℓ : ℝ) : ∃ b θ : ℝ, 0 ≤ b ∧
    ∀ (o : V → Site (H.S.side j p)) (D : Hot R → Pulse G _) (L : V → Pulse G _), Specified H j p N o D L ℓ →
      ∃ Z, ∀ i : Hot (parts R), Passage H j p N o D L Z i θ b (Z i) := by
  obtain ⟨θ,hp,hθ⟩ := haloed (G:=G) (n:=H.S.side j p) (H.rep N p j).p
  obtain ⟨b,hb,hf⟩ := descend H R j p N h he hp (fun x y => hθ y x) ℓ (Fintype.card (Hot R))
  refine ⟨_,θ,hb,fun o D L he => ?_⟩; obtain ⟨Z,hZ⟩:=hf _ _ _ he
  exact ⟨Z,fun i => hZ i (card_le_univ _)⟩
end YM.Multi.Step
