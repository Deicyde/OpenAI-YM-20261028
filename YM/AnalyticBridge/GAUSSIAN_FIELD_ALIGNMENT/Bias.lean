import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.BiasBase
import YM.Next.ROTATIONS.Tunnel
import YM.Push.BETA_TRANSPORT.Controlled
import YM.Push.LOCAL_SPLITTING.Raw
import YM.Push.PRICE_COMPILER.Powers
import YM.UVNext.PRICED_KERNELS.Read

set_option warningAsError false

/-!
# Spend the ordered-window cost on the actual affine source

More E:, at order 0. Compares two real shifts on the intact
frozen boundary extension; exponential in the contained coarse radius and
including true summable path lengths in the calculation. Also give an
explicit density trade price when changing centers at coupling g: its sizes
depend on that change IN RESCALED UNITS. Does not assume a fixed numerical g
applies at all heights.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Bias
open Function Filter Set Lattice Wilson RG Precision Exterior Tree Matrix Pressure Pressure.Tube Pressure.Stores Bid
open Next.Fluctuations Push.SectorMeasure Next.SectorChange Motion Rows Wisps Schur Gaussian LocalJet BiasBase Relative
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma settle_max (S : StepData c f) (s : Signed) (U : Config G f) (p : Site c) (v : ℕ) (a : Directions G f) :
    settle S p v (inChannel s U a) ≤ chips S v*‖a‖ := by
  calc
    _ ≤ ∑ i ∈ members S p v, ‖a‖ := Finset.sum_le_sum fun _ _ => (in_size ..).trans_le (norm_le_pi_norm ..)
    _ ≤ _ := by rw [Finset.sum_const,nsmul_eq_mul]; gcongr; exact saves ..


lemma kicks (d : Patch) (P : Teller G) (hg : d.Branches P.bind G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=d → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ (i : Slots S), keep x (shots S x) A F i → ∀ a : Directions G f, ‖bump T x V k a i‖ ≤ C*‖a‖ := by
  obtain ⟨B,hb,H⟩ := face_global G
  obtain ⟨C,δ,hc,hδ,h⟩ := earned d P.bind G hg
  let D (r) := (Fintype.card (Site d.L):ℝ)*(grain r * Fintype.card Axis)
  have hn (r) : 0 ≤ D r := by unfold D grain; positivity
  have ht : 0 ≤ Knob P := P.top.paths_pos.le.trans (le_max_left ..)
  refine ⟨max (Knob P*(B*D 1)) (Real.sqrt P.bind.penalty*(C*D (predReach d))), le_max_of_le_left (mul_nonneg ht (mul_nonneg hb.le (hn _))),?_⟩
  filter_upwards [small_span d, Work.E01.radiusB_tendsto.eventually_ge_atTop (allot d+1), delay_temp G (E:=permit d) hδ] with x hx hu hδ
  intro c f S T hd hL hT A F k V hV i hi a
  obtain ⟨s,p|p⟩ := i
  let U := pull s 0 (replica S.ratio V)
  have he v : chips S v=D v := by unfold D chips; rw [show Fintype.card (Site S.patch.L)=_ from congr_arg (fun d : Patch => Fintype.card (Site d.L)) hd]
  · have hP (p : Cell f) : ‖plaquetteJet S V s p a‖ ≤ B*D 1*‖a‖ := by
      rw [plaquetteJet,(Motion.plaquette_turn s V p (face_smooth U p).contDiffAt).2, mul_assoc]
      refine (H S p _ _).trans (mul_le_mul_of_nonneg_left ?_ hb.le)
      rw [← he]; exact settle_max ..
    change ‖faceKick T x V a s p‖ ≤ _
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
    unfold faceKick; rw [mul_assoc (Knob P)]; split
    · obtain ⟨l,m,H1,-⟩ := hT.feeds
      have hp := hn 1
      refine (barrel_cost _ H1 _ _ (fun i => plaquetteJet S V s i a) _ (by positivity : 0 ≤ B*D 1*‖a‖) (fun i _ => hP _)).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),hT.high]
    exact mul_le_mul (le_max_right ..) (hP _) (norm_nonneg _) ht
  obtain ⟨_,hb',hf⟩ := (h S hd hT.knobs F A V x hV hx (by omega) (by omega) hδ).noise s k p hi
  change ‖noiseKick V k a s p‖ ≤ _
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
  rw [noiseKick,blockJet,(block_turn s V p k hb').2,norm_neg,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc,mul_assoc,hT.knobs]
  apply mul_le_mul_of_nonneg_left ((hf _).trans (mul_le_mul_of_nonneg_left ?_ hc.le)) (Real.sqrt_nonneg _)
  exact (settle_max ..).trans_eq (by unfold chips; rw [show Fintype.card (Site S.patch.L)=_ from congr_arg (fun d : Patch => Fintype.card (Site d.L)) hd,hd])

lemma frozen_cost (S : StepData c f) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (Y : LinkArray G (Frozen A x F)) (q : Chi) (d : ℝ) (hd : 0<d) :
    ‖input x A F (autoShell q d V Y)‖ ≤ 2*d := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro e; unfold input; split
  · split
    · exact patched_small q hd _
    rw [norm_zero]; positivity
  rw [norm_zero]; positivity

lemma sources (d : Patch) (P : Teller G) (hg : d.Branches P.bind G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=d → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ (q : Chi) (l : ℝ) (Y : LinkArray G (Frozen A x F)), 0<l → ‖Rows.source T x V k (shots S x) A F q l Y‖ ≤ C*(temp x+l) := by
  obtain ⟨B,hb,Hb⟩ := bases P d hg
  obtain ⟨C,hC,Hc⟩ := kicks d P hg
  refine ⟨slip*(B+2*C),by have := slip_pos; positivity,?_⟩
  filter_upwards [Hb,Hc] with x H h
  intro c f S T hd hl hT A F k V hV q l Y ht
  let a := input x A F (autoShell q l V Y)
  have h0 := Work.E04.temp_nonneg x
  have hs := slip_pos
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have hv {v : G.Color} (j : G.ColorIndex) : ‖v j‖ ≤ ‖v‖ := UVNext.PricedKernels.color_component ..
  rw [Rows.source,tape_read]; apply (hv _).trans
  unfold Rows.restrict; split
  next hi =>
    have ha := frozen_cost S x A F V Y q l ht
    rw [norm_smul,Real.norm_of_nonneg hs.le,mul_assoc,Pi.add_apply]; apply mul_le_mul_of_nonneg_left _ hs.le
    exact ((norm_add_le ..).trans (add_le_add (H S T hd hT hl V A F hV k i.1 hi) (h S T hd hl hT A F k V hV i.1 hi a))).trans (by change B*temp x + C*‖a‖ ≤ _; have hi : ‖a‖ ≤ 2*l := ha; nlinarith)
  rw [norm_zero]; positivity

/-- Actual affine source/bias cost in physical coordinates, not just a
resolvent or row coefficient estimate. No derivative spent on selection. -/
theorem sources_read (d : Patch) (P : Teller G) (hg : d.Branches P.bind G) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=d → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    ∀ (q : Chi) (l : ℝ) (Y : LinkArray G (Frozen A x F)), 0<l → ‖blame T x V k (shots S x) A F q l Y‖ ≤ C*(temp x+l) := by
  obtain ⟨C,hC,Hc⟩ := sources d P hg
  obtain ⟨D,δ,hD,hδ,H⟩ := written P.bind d G P hg
  let σ := P.top.width; have hσ : 0 < σ := P.top.width_pos
  let E := (Fintype.card G.ColorIndex:ℝ) * ((Fintype.card Signed:ℝ)*
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site d.L) * Tier.wealth (σ/2))+
      Fintype.card Axis * Tier.wealth (σ/2)))
  let E' := ((Fintype.card G.ColorIndex:ℝ)*(Fintype.card (Site d.L)*Fintype.card Axis))*Tier.wealth (σ/2)
  let cost := max E' E *D
  have hE := Tier.wealth_nn (σ/2)
  have he : 0 ≤ cost := mul_nonneg (le_max_of_le_left (by unfold E'; positivity)) hD
  refine ⟨cost*C,mul_nonneg he hC,?_⟩
  filter_upwards [Hc, small_span d, Work.E01.radiusB_tendsto.eventually_ge_atTop (allot d+1), delay_temp G (E:=permit d) hδ] with x Hc hx hx' hδ
  intro c f S T hd hl hT A F k V hV q l Y h
  let L := move T x V k (shots S x) A F
  let a := Rows.source T x V k (shots S x) A F q l Y
  have hh := H S T hd hT.knobs hT A V F x hV hx (by omega) (by omega) hδ k
  have hw : Pours L (down S) (front A F) 0 cost := by
    have hy := Schur.pure hσ hD hh (Tier.down_price (σ/2) (by positivity) S G) (Tier.front_price (σ/2) (by positivity) A F G (x:=x))
    apply hy.weaker (by positivity) (le_of_eq ?_); unfold cost Tier.slotFee Tier.keyFee; rw [show Fintype.card (Site S.patch.L)=_ from congr_arg (fun d : Patch => Fintype.card (Site d.L)) hd,max_comm]
  have ht := Work.E04.temp_nonneg x
  rw [pi_norm_le_iff_of_nonneg (by positivity)]; intro j
  calc
    _ ≤ ∑ i, |L i j * a i| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i, |L i j| * ‖a‖ := Finset.sum_le_sum fun i _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm a i) (abs_nonneg _)
    _ ≤ cost*(C*(temp x+l)) := by rw [← Finset.sum_mul]; exact mul_le_mul (by simpa [rate] using hw.col j) (Hc S T hd hl hT A F k V hV q l Y h) (norm_nonneg _) he
    _ = _ := (mul_assoc ..).symm

-- deterministic window and translated price arithmetic.
section cost
variable {α : Type} [Fintype α] [DecidableEq α] {p : α → Site c} {s r M : ℝ}
variable {W W' : α → Set α} {A : Gaussian.Table α}

lemma station (h : Supported A W p r s M) (hs : 0 ≤ s) (b : Vec α) :
    ‖A *ᵥ (- (Schur.per W A).transpose *ᵥ b) + b‖ ≤ M*(M*Real.exp (-s*r))*‖b‖ := by
  have he := h.tail.turn
  rw [Matrix.transpose_sub, transpose_nonsing_inv,(Matrix.isHermitian_iff_isSymm.mp h.source_pos.isHermitian).eq] at he
  have hv := Relative.source hs (h.prec.fuse he hs).turn b
  rw [Matrix.transpose_transpose,Matrix.neg_mulVec,Matrix.mul_sub,Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ h.source_pos.det_pos.ne'),Matrix.sub_mulVec,Matrix.one_mulVec, ← mulVec_mulVec, neg_sub] at hv
  rwa [Matrix.neg_mulVec, Matrix.mulVec_neg,add_comm,← sub_eq_add_neg]

lemma means (ha : Supported A W p r s M) (hb : Supported A W' p r s M) (hs : 0 ≤ s) (b : Vec α) :
    ‖-(per W A).transpose *ᵥ b - (-(per W' A).transpose *ᵥ b)‖ ≤ 2*(M*Real.exp (-s*r))*‖b‖ := by
  have H := (of_pours ha.tail).sub (of_pours hb.tail); rw [sub_sub_sub_cancel_right,← two_mul] at H
  rw [show -_ *ᵥ b - (-_ *ᵥ b)=-(per W A-per W' A).transpose *ᵥ b by rw [transpose_sub,neg_sub,sub_mulVec,neg_mulVec,neg_mulVec]; abel]
  exact Relative.source hs (to_pours H (by have := ha.order.pos; positivity)) b

omit [DecidableEq α] in
lemma sumSq_max (v : Vec α) : sumSq v ≤ Fintype.card α*‖v‖^2 := by
  unfold sumSq; rw [show (Fintype.card α:ℝ)*‖v‖^2 = ∑ _i : α, ‖v‖^2 by simp]
  exact Finset.sum_le_sum fun i _ => by rw [← sq_abs]; exact pow_le_pow_left₀ (norm_nonneg (v i)) (norm_le_pi_norm v i) _

/-- Allow a translated price (μ's built from the same b). Both the force
and determinant quotient are retained; small (elliptic) tails at anchored
order zero. No claim the resulting exponential bound alone is a summable
integrand, e.g. before paying the coupling factor. -/
lemma trade_means (ha : Supported A W p r s M) (hb : Supported A W' p r s M) (hs : 0 ≤ s) (hr : 0 ≤ r) (b z : Vec α)
    {g K : ℝ} (hg : 0 < g) (hK : ‖b‖ ≤ K) :
    let θ := Real.exp (-s*r); let N : ℝ := Fintype.card α
    let U := per W A; let V := per W' A; let m := -U.transpose *ᵥ b; let m' := -V.transpose *ᵥ b
    |Real.log (trade (Relative.symPart U) (Relative.symPart V) (g⁻¹ • (m'-m)) z)| ≤
      (N+sumSq z)*(error M s r 0/2) + θ * M * (N*(g⁻¹*(2*M*K))^2 + sumSq z/2) := by
  intro θ N U V m m'
  let y := θ⁻¹ • g⁻¹ • (m'-m)
  have h := Relative.compare ha hb (to_pours (by rw [sub_self]; exact FreeResolvent.Cost.Schur.zero le_rfl) le_rfl) hs
  have ht : 0 < θ := Real.exp_pos _
  have he : θ^2 ≤ θ := by have hy : θ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hr); nlinarith
  rw [show g⁻¹ • (m'-m)=θ • y from by unfold y; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]]
  apply (h.priceShift ha.charges hs θ y z).trans
  rw [abs_of_pos ht, add_le_add_iff_left]; have hM := ha.order.pos
  have hy : ‖y‖ ≤ g⁻¹ * (2*M*K) := by
    unfold y; rw [norm_smul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le,Real.norm_of_nonneg (inv_pos.mpr hg).le]
    calc
      _ ≤ θ⁻¹*(g⁻¹*(2*(M*θ)*K)) := by gcongr; exact (means hb ha hs b).trans (mul_le_mul_of_nonneg_left hK (by positivity))
      _ = _ := by field_simp
  have hh := (sumSq_max y).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) (show 0 ≤ N from Nat.cast_nonneg _))
  change sumSq y ≤ N*_ at hh
  have hz := sumSq_nn y
  nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hM hz), mul_le_mul_of_nonneg_left hh (mul_nonneg ht.le hM)]
end cost

/-- At eligible cells compare both *actual* translated Gaussian prices
using the sector nonlinear/kernel constructions. Does not change tagged
large-field data or integrate dV. Use `Ready.change` for exact integrals incl
moving centers. The last term still tracks chart size / coupling (and actual
regular volume), not a budget with those silently erased. -/
theorem advanced (P : Teller G) (d : Patch) (h : d.Branches P.bind G) :
    ∃ s η M D K : ℝ, 0<s ∧ 0<η ∧ 0<M ∧ 0≤D ∧ 0 ≤ K ∧ ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Larger (G:=G) S → S.patch=d → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    Ready A F x T k V s η M D ∧ ∀ (q : Chi) (l : ℝ) (Y : LinkArray G (Frozen A x F)), 0<l →
      let b := blame T x V k (shots S x) A F q l Y; let C := K*(temp x+l); let Q := Rows.gram T x V k (shots S x) A F
      let m := meanLog A F T x V k q l Y; let m' := middleLog A F x T V k q l Y
      let r : ℝ := ((radiusB x /60:ℕ):ℝ); let θ := Real.exp (-s*r); let N : ℝ := Fintype.card (In x A F (G:=G))
      ‖b‖ ≤ C ∧ ‖m‖ ≤ M*C ∧ ‖m'‖ ≤ M*C ∧ ‖Q *ᵥ m + b‖ ≤ (M*(M*θ))*C ∧ ‖Q *ᵥ m'+b‖ ≤ (M*(M*θ))*C ∧
        ‖m-m'‖ ≤ 2*(M*θ)*C ∧ ∀ (z : Prices G (Active A x F)) (g : ℝ), 0 < g →
          |Real.log (trade (fog A F T x V k) (middle A F x T V k) (g⁻¹ • (m'-m)) z)| ≤
            (N+sumSq z)*(error M s r 0/2)+θ*M*(N*(g⁻¹*(2*M*C))^2 + sumSq z/2) := by
  obtain ⟨s,η,M,D,hs,hη,hM,hD,H⟩ := purchase P d h
  obtain ⟨K,hK,H'⟩ := sources_read d P h
  refine ⟨s,η,M,D,K,hs,hη,hM,hD,hK,?_⟩
  filter_upwards [H,H'] with x hx hy
  intro c f S T hL hd hc hT A F k V hA
  have h := hx c f S T hd hL hc hT A F k V (Or.inl hA)
  refine ⟨h,?_⟩; intro q l Y hl b C Q m m' r θ N
  have hC : ‖b‖ ≤ C := hy _ _ hd hc hT A F k V hA q l Y hl
  have ht : 0 < θ := Real.exp_pos _
  exact ⟨hC,(Relative.source hs.le h.ends.order b).trans (by gcongr), (Relative.source hs.le h.mids.order b).trans (by gcongr),
    (station h.ends hs.le b).trans (mul_le_mul_of_nonneg_left hC (by positivity)),
    (station h.mids hs.le b).trans (mul_le_mul_of_nonneg_left hC (by positivity)),
    (means h.ends h.mids hs.le b).trans (mul_le_mul_of_nonneg_left hC (by positivity)), fun z g hg => trade_means h.ends h.mids hs.le (Nat.cast_nonneg _) b z hg hC⟩
end YM.AnalyticBridge.GaussianFieldAlignment.Bias
