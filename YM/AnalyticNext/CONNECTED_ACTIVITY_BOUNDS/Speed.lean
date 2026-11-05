import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ReachD

/-!
# Point cost of D. Both weighted index and stencil incidence.

Uniform in *arbitrary* V. `P.width` of the top path price. All post-L
costs earned before any F/window. Extensive factors deliberately not
used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior
open Turn Work.F03 Progress.StationaryScenes Push.AbsoluteSums
open Green
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma lie_basis_cost (i : Vars G n) (z : Bond n) : ‖lie (Pi.single i (1:ℝ)) z‖ ≤ 1 := by
  by_cases h : i.1=z
  · subst z
    rcases i with ⟨p,l⟩
    have he : lie (Pi.single (p,l) (1:ℝ)) p = EuclideanSpace.basisFun _ ℝ l := by
      ext j
      change (Pi.single (p,l) 1 : ArrayR G n) (p,j) = _; simp [Pi.single_apply,EuclideanSpace.basisFun_apply]
    rw [he]; exact (OrthonormalBasis.norm_eq_one ..).le
  rw [lie_basis i z h]; simp

lemma piece_cost (x : G.Color) (i : G.ColorIndex) : |x i| ≤ ‖x‖ := calc
    _ = |inner ℝ ((EuclideanSpace.basisFun G.ColorIndex ℝ) i) x| := by simp only [EuclideanSpace.basisFun_inner]
    _ ≤ _ := (abs_real_inner_le_norm ..).trans_eq (by simp only [OrthonormalBasis.norm_eq_one,one_mul])

lemma curl_cost (p : Cell f) (x : Directions G f) (B : ℝ) (h : ∀ i, ‖x i‖ ≤ B) :
    ‖curl p x‖ ≤ 4*B := by
  rw [curl_chain]; unfold chain
  refine (norm_sub_le _ _).trans ?_
  apply le_trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _)); exact
    (add_le_add (add_le_add (h _) (h _)) (add_le_add (h _) (h _))).trans_eq (by ring)

lemma level_power (T : Tube G S) {P : Teller G} (h : P.Funds S T) (s : Signed) (V : Config G c) (R : ℕ)
    (α : ℝ) (ha : 0<α) (hh : α ≤ P.top.width) (i : Twin f) (j : Vars G f) :
    let p : Pos S := (s,.inl i)
    wt α (base S p) (home S j.1) * ‖level T R i (untwine S p V (lie (Pi.single j 1)))‖ ≤
      (4*Real.exp (α*2)*Real.sqrt P.top.clip.direct + P.top.paths*4) := by
  intro p
  let x := untwine S p V (lie (Pi.single j 1)); let y := untwine S p V (0:Directions G f)
  have he m : ‖x m‖ ≤ 1 := by unfold x; rw [pull_cost]; exact lie_basis_cost ..
  have hy : y=0 := by funext; simp [y,untwine, rotateG]
  let w := wt α (base S p) (home S j.1)
  have hw : 0 < w := wt_pos ..
  have hv := P.top.paths_pos
  have hL := P.top.clip.quadratic_pos
  have hm (l : ℕ) : (w*‖bandTerm T R i.1 l x‖) ≤ |(T.up.row i.1.2 l).1| * Real.exp (P.top.width * (T.up.row i.1.2 l).2.length)*4 := by
    by_cases hz : separation (base S p) (home S j.1) ≤ (T.up.row i.1.2 l).2.length
    · have ht : w ≤ Real.exp (P.top.width * (T.up.row i.1.2 l).2.length) := by
        unfold w wt; have h := P.top.width_pos; gcongr
      unfold bandTerm; split
      next h =>
        have hr := curl_cost (slotFace (T.up.row i.1.2 l).2 i.1.1) x 1 he
        rw [mul_one] at hr
        rw [norm_smul]; refine (mul_le_mul ht (mul_le_mul_of_nonneg_left hr (norm_nonneg _)) (by positivity) (by positivity)).trans_eq ?_
        rw [Real.norm_eq_abs]; ring
      next h => rw [norm_zero,mul_zero]; positivity
    have h := slot_range T R p i rfl V l (lie (Pi.single j 1)) 0 (by
      intro j' hj'; apply lie_basis j j'
      rintro he; rw [← he] at hj'; contradiction)
    change bandTerm T _ _ _ x=bandTerm T _ _ _ y at h
    rw [h,hy]; unfold bandTerm; split
    next h => simp only [curl_chain,chain, Pi.zero_apply,sub_zero,smul_zero,norm_zero,mul_zero]; positivity
    next h => rw [norm_zero,mul_zero]; positivity
  have hi := h.feeds; obtain ⟨L,A,h1,h2⟩ := hi
  unfold level; split
  next hx =>
    change w * ‖∑' l, bandTerm T R i.1 l x‖ ≤ _
    let b l := |(T.up.row i.1.2 l).1| * Real.exp (P.top.width * (T.up.row i.1.2 l).2.length)
    have hs : SumBudget b P.top.paths := h1.rows _
    have hg := (hs.2.1.mul_right 4).of_nonneg_of_le (fun l => mul_nonneg hw.le (norm_nonneg (bandTerm T R _ l x))) hm
    have hx : Summable (fun l => ‖bandTerm T R i.1 l x‖) := by
      have hh := hg.mul_left w⁻¹
      simpa only [inv_mul_cancel_left₀ hw.ne'] using! hh
    calc
      _ ≤ w * ∑' l, ‖bandTerm T R i.1 l x‖ := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hx) hw.le
      _ ≤ (∑' l, b l)*4 := by
        rw [← tsum_mul_left, ← tsum_mul_right]; exact hg.tsum_le_tsum hm (hs.2.1.mul_right 4)
      _ ≤ P.top.paths*4 := by gcongr; exact hs.2.2
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  next hx =>
    change w * ‖Real.sqrt T.high.direct • curl i.1 x‖ ≤ _; rw [h.high, norm_smul]
    by_cases hs : separation (base S p) (home S j.1) ≤ 2
    · have hm : w ≤ Real.exp (α*2) := by unfold w wt; gcongr; exact_mod_cast hs
      rw [Real.norm_of_nonneg (by positivity)]
      have ht := curl_cost i.1 x 1 he; rw [mul_one] at ht
      calc
        _ ≤ Real.exp (α*2) * (Real.sqrt P.top.clip.direct*4) := by gcongr
        _ = 4*Real.exp (α*2)*Real.sqrt P.top.clip.direct := by ring
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    have hi : curl i.1 x=curl i.1 y := by
      apply curl_range S; intro z hz; apply pull_dep
      apply lie_basis j (edgeP s z); intro hg; apply hs; rw [hg]
      have h := along_home s (S.ratio.parent i.1.1) S z
      exact h.trans (by omega)
    rw [hi,hy,curl_chain]; simp only [chain,Pi.zero_apply,sub_zero,norm_zero,mul_zero]; positivity

/-- I row rooted predictor reads, keep locality even if tag
families in the inputs vary. Post at this patch shape. -/
lemma noise_power (D : Patch) (K : KernelChoices) (G : Gauge) (hb : D.Branches K G) (α : ℝ) (ha : 0<α) :
    ∃ C : ℝ, 0<C ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.kernel=K → S.patch=D →
    ∀ (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Vars G f),
      let p : Pos S := (s,.inr i)
      wt α (base S p) (home S j.1) * ‖derivative T R p V (lie (Pi.single j 1))‖ ≤ C := by
  obtain ⟨E,r,hE,-,hx⟩ := Next.Fluctuations.z_chart_cost D K G hb
  refine ⟨Real.exp (α*(Next.Fluctuations.predReach D+1:ℕ))*E,by positivity,?_⟩
  intro c f S T hK hD s V R i j p
  let x := untwine S p V (lie (Pi.single j 1))
  have hi m : ‖x m‖ ≤ 1 := by unfold x; rw [pull_cost]; exact lie_basis_cost ..
  change _ * ‖Next.Fluctuations.zLin S (form x) 0 i‖ ≤ _
  by_cases hl : separation (base S p) (home S j.1) ≤ Next.Fluctuations.predReach S.patch+1
  · have hm : ‖(form x, (0:fieldDir G c 1))‖ ≤ 1 := by
      change max _ _ ≤ _; rw [norm_zero]; refine max_le ?_ zero_le_one
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      exact fun _ => hi _
    obtain ⟨q,-⟩ := hx c f S hD hK (Classical.ofNonempty:S.Choices) i (form x,0)
    apply mul_le_mul _ (q.trans (mul_le_of_le_one_right hE.le hm)) (by positivity) (Real.exp_pos _).le
    unfold wt; rw [hD] at hl; gcongr
  have hz : Next.Fluctuations.zLin S (form x) 0 i = Next.Fluctuations.zLin S (form (0:Directions G f)) 0 i := by
    apply z_range (by rw [hK,hD]; exact hb); intro z hz
    have he := along_home s i.1 S z
    have ht : edgeP s z≠j.1 := fun e => hl (le_trans (show separation _ _ ≤ _ from e ▸ he) (by omega))
    apply norm_eq_zero.mp
    unfold x; rw [pull_cost, lie_basis j _ ht.symm]; simp
  have he : Next.Fluctuations.zLin S (form (0:Directions G f)) 0 i=(0:G.Color) := by
    ext u
    simp only [Next.Fluctuations.zLin,PiLp.smul_apply,PiLp.sub_apply,Pi.zero_apply,PiLp.zero_apply];
    rw [show parts G 1 (form (0:Directions G f)) u = 0 from rfl]; simp
  rw [hz,he,norm_zero,mul_zero]; positivity

-- point exp uses even for unfolded operations. α/width paid by any top.
theorem received (P : Teller G) (D : Patch) (hm : D.Branches P.bind G) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (x : ℝ) (V : Config G c) (i : Ix G S) (j : Vars G f),
      wt P.top.width (base S i.1) (home S j.1) * |scale T x V i j| ≤ C := by
  obtain ⟨C,hc,he⟩ := noise_power D P.bind G hm P.top.width P.top.width_pos
  let A := (4*Real.exp (P.top.width*2)*Real.sqrt P.top.clip.direct + P.top.paths*4)
  refine ⟨Real.sqrt weight*max C A, mul_pos (Real.sqrt_pos.mpr weight_pos) (hc.trans_le (le_max_left ..)),?_⟩
  intro c f S T h hD x V i j
  let v := derivative T (till x) i.1 V (lie (Pi.single j 1)); let w := wt P.top.width (base S i.1) (home S j.1)
  have hp : w*‖v‖ ≤ max C A := by
    rcases i with ⟨⟨s,i|i⟩,k⟩
    · exact le_trans (level_power T h s V _ _ P.top.width_pos le_rfl _ j) (le_max_right ..)
    exact (he c f S T h.knobs hD s V _ i j).trans (le_max_left ..)
  change w*|Real.sqrt weight * v i.2| ≤ _
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left (piece_cost ..) (wt_pos ..).le).trans hp) (by positivity)

end YM.AnalyticNext.ConnectedActivity.Aff
