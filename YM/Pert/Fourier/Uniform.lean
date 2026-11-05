import YM.Pert.Fourier.Steps
/-! Uniform rescaled Fourier-shell derivative bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Function Filter Set Metric Topology
open scoped ContDiff
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {t : ℝ}
lemma compactCost (n : ℕ) {f : ℝ→E4→ℂ} {S : Set E4} (hS : IsCompact S)
  (L : Set ℝ) (hL : IsCompact L) (h : Smooth n (L ×ˢ S) (uncurry f)) :
    ∃ C > 0, ∀ p ∈ L ×ˢ S, ‖iteratedFDeriv ℝ n (f p.1) p.2‖ ≤ C := by
  classical
  suffices he : ∀ (V : Type) [i : NormedAddCommGroup V] [j : NormedSpace ℝ V] (f : ℝ→E4→V) (_ : Smooth n (L ×ˢ S) (uncurry f)),
      ∃ C > 0, ∀ p ∈ L ×ˢ S, ‖iteratedFDeriv ℝ n (f p.1) p.2‖ ≤ C by exact he ℂ _ h
  clear h f
  induction n with
  | zero =>
    intro V _ _ f h
    obtain ⟨C,hC⟩ := (hL.prod hS).exists_bound_of_continuousOn (fun p hp => (h p hp).continuousAt.continuousWithinAt)
    exact ⟨max C 1,lt_max_of_lt_right zero_lt_one,fun p hp => by rw [norm_iteratedFDeriv_zero]; apply le_trans (hC _ hp) (le_max_left C 1)⟩
  | succ n ih =>
    intro V _ _ f h
    let g : ℝ→E4→ (E4→L[ℝ]V) := fun t => fderiv ℝ (f t)
    have hg : Smooth n (L ×ˢ S) (uncurry g) := fun x hx => by
      let F : (ℝ×E4)→ E4→V := fun a z => f a.1 z
      have H := (h x hx).comp (f:=fun p : (ℝ×E4)×E4=>(p.1.1,p.2)) (g:=uncurry f) (x,x.2) ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
      exact ContDiffAt.fderiv (f:=F) (g:=Prod.snd) H (contDiffAt_snd (𝕜:=ℝ)) (by norm_cast)
    obtain ⟨C,hCp,hC⟩ := ih _ (g) hg
    refine ⟨C,hCp,?_⟩
    simpa only [g,norm_iteratedFDeriv_fderiv] using! hC

lemma middle_bound (n : ℕ) (D : List Axis) :
    ∃ C > 0, ∀ p : ℝ×E4, p.1∈ Icc (0:ℝ) 1 → p.2∈closedBall 0 6 → ‖iteratedFDeriv ℝ n (middle D p.1) p.2‖ ≤ C := by
  obtain ⟨C,hC,he⟩ := compactCost n (isCompact_closedBall (0:E4) (6:ℝ)) _ (isCompact_Icc (a:=(0:ℝ)) (b:=(1:ℝ))) (f:=middle D) (fun p hp => ContDiffAt.of_le (middle_diff D p.1 (by rw [abs_of_nonneg hp.1.1]; exact hp.1.2) p.2) (by norm_cast; simp))
  · exact ⟨C,hC,fun q h h' => he q ⟨h,h'⟩⟩
def cap : ℝ := 5 * Real.pi / 4
def box (t : ℝ) := {x : E4 | ∀ i, |t * x i| ≤ cap}
lemma cap_pos : 0 < cap := by unfold cap; positivity
lemma convex_box (t : ℝ) : Convex ℝ (box t) := by
  have ht : box t = ⋂ i : Axis, (⇑(t • (EuclideanSpace.proj (𝕜:=ℝ) i).toLinearMap) ⁻¹' Icc (-cap) cap) := by ext x; simp only [mem_iInter,mem_preimage,mem_Icc]; exact forall_congr' fun i => abs_le
  rw [ht]
  apply convex_iInter
  exact fun i => (convex_Icc _ _).linear_preimage _
lemma bound_box {x : E4} (h : x ∈ box t) (ht : t ∈ Icc (1/2:ℝ) 1) : x ∈ closedBall 0 (5*cap) := by
  have he (i : Axis) : |x i| ≤ 2*cap := by have hi := h i; rw [abs_mul,abs_of_nonneg (by linarith [ht.1])] at hi; nlinarith only [ht.1,hi,abs_nonneg (x i)]
  simp only [mem_closedBall,dist_zero_right]
  grw [←sq_le_sq₀ (norm_nonneg _) (by have := cap_pos; positivity : 0≤5*cap), Full.norm_four]
  apply le_trans (Finset.sum_le_sum (g:=fun i => (2*cap)^2) (fun i hi => by rw [sq_le_sq,abs_of_pos (by have := cap_pos; positivity : 0<2*cap)]; exact he i))
  have := cap_pos; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; norm_cast; push_cast; nlinarith [sq_nonneg cap]
def domain := (Icc (1/2:ℝ) 1 ×ˢ Set.univ (α:=E4)) ∩ {v | v.2 ∈ box v.1}
lemma domain_subset : domain ⊆ Icc (1/2:ℝ) 1 ×ˢ closedBall (0:E4) (5*cap) := fun _ h => ⟨h.1.1,bound_box h.2 h.1.1⟩
lemma domain_compact : IsCompact domain := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc.prod (isCompact_closedBall (0:E4) (5*cap))) ?_ domain_subset
  apply IsClosed.inter (isClosed_Icc.prod isClosed_univ)
  rw [show {v : ℝ×E4 | v.2 ∈ box v.1} = ⋂ i, {v : ℝ × E4 | |v.1*v.2 i| ≤ cap} by ext v; simp [box]]
  exact isClosed_iInter fun i=> isClosed_le (by fun_prop) continuous_const
lemma last_bound (n : ℕ) (D : List Axis) :
   ∃ C > 0, ∀ p ∈ domain, ‖iteratedFDeriv ℝ n (last D p.1) p.2‖ ≤ C := by
  classical
  suffices he : ∀ (V : Type) [i : NormedAddCommGroup V] [j : NormedSpace ℝ V] (f : ℝ→E4→V) (_ : Smooth n domain (uncurry f)),
      ∃ C > 0, ∀ p ∈ domain, ‖iteratedFDeriv ℝ n (f p.1) p.2‖ ≤ C by
    apply he; intro x hx; apply (last_diff D x.1 x.2 (fun i => (hx.2 i).trans_lt (by unfold cap; linarith [Real.pi_pos]))).of_le; norm_cast; simp
  clear D
  induction n with
  | zero =>
    intro V _ _ f h
    obtain ⟨C,hC⟩ := domain_compact.exists_bound_of_continuousOn (fun p hp => (h p hp).continuousAt.continuousWithinAt)
    exact ⟨max C 1,lt_max_of_lt_right zero_lt_one,fun p hp => by rw [norm_iteratedFDeriv_zero]; apply le_trans (hC _ hp) (le_max_left C 1)⟩
  | succ n ih =>
    intro V _ _ f h
    let g : ℝ→E4→ (E4→L[ℝ]V) := fun t => fderiv ℝ (f t)
    have hg : Smooth n domain (uncurry g) := fun x hx => by
      let F : (ℝ×E4)→ E4→V := fun a z => f a.1 z
      have H := (h x hx).comp (f:=fun p : (ℝ×E4)×E4=>(p.1.1,p.2)) (g:=uncurry f) (x,x.2) ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
      exact ContDiffAt.fderiv (f:=F) (g:=Prod.snd) H (contDiffAt_snd (𝕜:=ℝ)) (by norm_cast)
    obtain ⟨C,hCp,hC⟩ := ih _ (g) hg
    refine ⟨C,hCp,?_⟩
    simpa only [g,norm_iteratedFDeriv_fderiv] using! hC
end YM.Pert.Band
