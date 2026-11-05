import YM.Org.Input

/-! Finite column limits at each fixed station, on the fixed Order. A finer
filter can be used in arithmetic WITHOUT changing the extraction. -/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set MeasureTheory Extraction
open scoped Topology ContDiff BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)]

abbrev Code := (i : ι) → Fin (Module.finrank ℂ (E i))

def combination (j : Code E) (i : ι) := (Module.finBasis ℂ (E i)) (j i)

def coords (j : Code E) (v : (i : ι) → E i) := ∏ i, (Module.finBasis ℂ (E i)).repr (v i) (j i)

theorem basis_tuple (v : (i : ι) → E i) (M : MultilinearMap ℂ E ℂ) :
    M v = ∑ i : Code E, coords E i v * M (combination E i) := by
  have he : v = fun i => ∑ j, (Module.finBasis ℂ (E i)).repr (v i) j • Module.finBasis ℂ (E i) j :=
    funext fun i => ((Module.finBasis ℂ (E i)).sum_repr _).symm
  conv_lhs => rw [he]
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl; intro i _
  exact M.map_smul_univ _ _

variable {α : Type*} {𝓛 : Filter α}

omit [DecidableEq ι] in
lemma tendsto_coords {p : (i : ι) → E i} {v : α → (i : ι) → E i} (j : Code E)
    (hv : ∀ i : ι, Tendsto (fun a => v a i) 𝓛 (𝓝 (p i))) :
    Tendsto (fun a => coords E j (v a)) 𝓛 (𝓝 (coords E j p)) :=
  tendsto_finsetProd _ fun i _ => ((Module.finBasis ℂ (E i)).coord (j i)).continuous_of_finiteDimensional.continuousAt.tendsto.comp
    (hv i)

lemma tendsto_multi [𝓛.NeBot] (F : α → MultilinearMap ℂ E ℂ) (f : ((i : ι) → E i) → ℂ)
    (h : ∀ x, Tendsto (fun i => F i x) 𝓛 (𝓝 (f x))) (p : (i : ι) → E i) (v : α → (i : ι) → E i)
    (hv : ∀ i, Tendsto (fun a => v a i) 𝓛 (𝓝 (p i))) :
    Tendsto (fun a => F a (v a)) 𝓛 (𝓝 (f p)) := by
  let x := ∑ i : Code E, coords E i p * f (combination E i)
  have he (v : α → (i : ι) → E i) (hh : ∀ i, Tendsto (fun a => v a i) 𝓛 (𝓝 (p i))) :
      Tendsto (fun a => F a (v a)) 𝓛 (𝓝 x) := by
    simp_rw [basis_tuple E (v _)]; exact tendsto_finsetSum _ (fun i _ => (tendsto_coords E _ hh).mul (h _))
  rw [tendsto_nhds_unique (h p) (he (fun _ => p) fun _ => tendsto_const_nhds)]
  exact he _ hv

section Smear
variable {G : Gauge} {C : Family G} {n : ℕ} {S : Table C.book} {d : Caps n} {F : Extraction.Order}

/-- Multilinearity of the actual finite measurements. -/
private def finiteMoment (C : Family G) (N p : ℕ) (d : Caps n) (t : Test n) : Moment C.book n d :=
  ((C.S.a N:ℂ)^(4*n)) • ∑ r : Fin n → Lattice.Site (C.side N p), t (Order.cells C N p r) • C.ensemble d r

private lemma finiteMoment_eq (t : Test n) (x : C.book.Vector d) (N p : ℕ) :
    Order.smears C N p (fun i => ⟨d i,x i⟩) t = finiteMoment C N p d t x := by
  unfold finiteMoment Order.smears
  simp only [_root_.smul_apply,_root_.sum_apply, smul_eq_mul]
  rfl

lemma calibrated_smear (h : F.Ordered C S) (b : Filter (ℕ×ℕ)) [b.NeBot] (hp : b ≤ F.fuse)
    (t : Test n) {v : ℕ×ℕ → C.book.Vector d} {x : C.book.Vector d}
    (he : ∀ i : Fin n, Tendsto (fun j => v j i) b (𝓝 (x i))) :
    Tendsto (fun u : ℕ×ℕ => Order.smears C u.1 u.2 (fun i => ⟨d i,v u i⟩) t) b
      (𝓝 (S.integralOn d x t)) := by
  have hz (x : C.book.Vector d) : Tendsto (fun u : ℕ×ℕ => finiteMoment C u.1 u.2 d t x) b (𝓝 (S.integralOn d x t)) := by
    simp_rw [← finiteMoment_eq]
    exact (Order.along (h.reads _ (fun i => ⟨d i,x i⟩) _)).mono_left hp
  simp_rw [finiteMoment_eq]
  exact tendsto_multi (ι:=Fin n) _ _ (fun y => S.integralOn d y t) hz x v he
end Smear

lemma finite_extract {Y : Type*} [NormedAddCommGroup Y] [ProperSpace Y] [𝓛.NeBot] (v : α → Y) (c : ℝ)
    (h : ∀ᶠ i in 𝓛, ‖v i‖ ≤ c) : ∃ b : Filter α, b ≤ 𝓛 ∧ b.NeBot ∧ ∃ x, Tendsto v b (𝓝 x) := by
  have he : ∀ᶠ i in 𝓛, v i ∈ Metric.closedBall 0 c := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using h
  obtain ⟨x,-,hx⟩ := (isCompact_closedBall ..).exists_mapClusterPt_of_frequently he.frequently
  obtain ⟨ℬ,hu,hB⟩ := mapClusterPt_iff_ultrafilter.mp hx
  exact ⟨↑ℬ,hu,inferInstance,x,hB⟩
end YM.Next.UVStress
