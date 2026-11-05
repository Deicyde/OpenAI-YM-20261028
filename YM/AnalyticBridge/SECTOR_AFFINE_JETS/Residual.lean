import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Covariance

/-!
# Cost on the genuine *selected Gaussian's own inverse*, and its multiplier defect

It's a symmetrized-window Gaussian, not a matrix inverse of the Gram in the
exponent. Need to price S, the C-inverse, and their terms in the density ratio
relative to the reference affine action. Don't swap the signs or compare to
some other choice of Gaussian. Here derive exponentially small bills with all
these external V jets. There's still substantial work to **sum** ratio label
expansions, estimate multiplers in active/frozen variables, etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Push.Uniform (bolt)
open YM.FreeResolvent (Mark Bundle native)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {x σ η d M u v l : ℝ}
variable {A : Stores S} {k : S.Choices} {V : Config G c} {B : PriceCoords G c}

abbrev pickedS (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ)
    (V : Config G c) (k : S.Choices) (z : PriceCoords G c) :=
  profileGram T x V A F k z * pickedCov A F T x V k z-1

/-- Matrix in the quadratic correction `Rows.adjustment`. -/
abbrev pickedDelta (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ)
    (V : Config G c) (k : S.Choices) (z : PriceCoords G c) :=
  (pickedCov A F T x V k z)⁻¹ - profileGram T x V A F k z

/- Convenience lemmas expose the matrix and normalization conventions.
Strengthen at all principal compressions. No nonempty index-set hypotheses. -/
section bounds

structure SlicePrice {ι : Type} [Fintype ι] (Q : Matrix ι ι ℝ) (η M : ℝ) : Prop where
  pos : Q.PosDef
  low (z : ι → ℝ) : η * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Q *ᵥ z)
  upper (z : ι → ℝ) : |z ⬝ᵥ (Q *ᵥ z)| ≤ M * (z ⬝ᵥ z)

lemma inner_price {k : ℕ} {ι : Type} [Fintype ι] (p : ι → Site c) (B : PriceCoords G c)
    {Q : PriceCoords G c → Matrix ι ι ℝ} (h : Polar B p p Q k d M) (hd : 0 ≤ d) (hs : YM.FreeResolvent.Gap (Q B) η)
    (he : 0 < η) (ht : (Q B).IsSymm) {ι' : Type} [Fintype ι']
    (t : ι' → ι) (hv : Injective t) : SlicePrice (limitTo Q t B) η M := by
  let L : Matrix ι' ι' ℝ := limitTo Q t B
  have ha : YM.FreeResolvent.Gap L η := hs.submatrix t hv
  have hx : L.IsSymm := ht.submatrix _
  exact ⟨Schur.dissolves (funded_gap ha) hx he, ha.lower,
    fun z => FreeResolvent.schur_qf (native c) (p ∘ t) (((polar_schur h).submatrix hv hv).mono hd le_rfl) z⟩

lemma KernelJets.compressed_prices {n : ℕ} (h : KernelJets n d v η l M A F T x V k B)
    (hd : 0 ≤ d) (he : 0 < η) (hl : 0 < l) {ι : Type} [Fintype ι]
    (t : ι → Rows.In x A F (G:=G)) (hv : Injective t) :
    SlicePrice (limitTo (profileGram T x V A F k) t B) η M ∧
      SlicePrice (limitTo (pickedCov A F T x V k) t B) l M := by
  constructor
  · apply inner_price (Wisps.front A F) B h.gramJets hd h.solvency he ?_ _ hv
    unfold Matrix.IsSymm profileGram Rows.gram; rw [transpose_mul,transpose_transpose]
  exact inner_price _ B h.cJets hd h.covSanction hl (Matrix.isHermitian_iff_isSymm.mp h.covPosDef.1) _ hv

lemma KernelJets.price_bounds {n : ℕ} (h : KernelJets n d v η l M A F T x V k B)
    (hd : 0 ≤ d) (he : 0 < η) (hl : 0 < l) :
    SlicePrice (profileGram T x V A F k B) η M ∧ SlicePrice (pickedCov A F T x V k B) l M :=
  h.compressed_prices hd he hl id injective_id
end bounds

section extendCost
variable {n : ℕ} {X : ℝ}

lemma KernelJets.cov_inverse (h : KernelJets n d v η l M A F T x V k B)
    (p : Price d M l σ 1 X 1 n)
    (hp : (native c).Volume (Wisps.front A F (G:=G) (x:=x)) σ X) {u : ℝ} (hu : 0 ≤ u) :
    ResolventJets (Wisps.front A F) B n σ (meter n n M 1 (rise X l)) u (action (pickedCov A F T x V k) u) :=
  cost_full hu h.cJets p hp h.covSanction

lemma KernelJets.funds_small (h : KernelJets n d v η l M A F T x V k B)
    (p : Price d M l σ 1 X 1 n) (hx : 0 < η)
    (hp : (native c).Volume (Wisps.front A F (G:=G) (x:=x)) σ X) :
    let s := σ/(n+1:ℕ)^2
    let M₁ := FreeResolvent.tagPrice 1 n M M
    let M₂ := FreeResolvent.tagPrice 1 n M₁ (meter n n M 1 (rise X l))
    let δ := Real.exp (-v * radiusB x)
    Polar B (Wisps.front A F) (Wisps.front A F) (pickedS A F T x V k) n s (M₁*δ) ∧
      Polar B (Wisps.front A F) (Wisps.front A F) (pickedDelta A F T x V k) n s (M₂*δ) := by
  intro s M₁ M₂ δ
  let C := meter n n M 1 (rise X l)
  let r := σ/(n+1:ℕ)
  have hs := p.pos; have hm := p.m
  have hr : 0 < r := by unfold r; positivity
  have ht : r+n*r=σ := by
    have he : r * (n+1:ℕ) = σ := div_mul_cancel₀ _ (by positivity : (n+1:ℕ) ≠ (0:ℝ))
    push_cast at he; linarith only [he]
  have h₀ : 0<s := by unfold s; positivity
  have hw : s+n*s=r := by
    have he : s= r/(n+1:ℕ) := by unfold s r; rw [div_div]; push_cast; ring
    have ht : s * (n+1:ℕ) = r := he ▸ div_mul_cancel₀ _ (by positivity : (n+1:ℕ) ≠ (0:ℝ))
    push_cast at ht; linarith only [ht]
  have h₁ : r ≤ σ := ht ▸ le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hr.le)
  have h₂ : s ≤ r := by
    calc s ≤ s + ↑n*s := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) h₀.le)
         _ = _ := hw
  have he := room_small p
  have hb : 0 ≤ δ := (Real.exp_pos _).le
  let a := Wisps.front A F (G:=G) (x:=x)
  let L := profileGram T x V A F k; let Q := pickedCov A F T x V k
  let L₀ (y) := (L y)⁻¹; let Q₀ (y) := (Q y)⁻¹
  let N := pickedS A F T x V k
  have hV : Polar B a a N n r (M₁*δ) := by
    have hL : Bundle bolt (marks G c r) (native c) a a L B n d M := Polar.toBundle h.gramJets (h₁.trans he)
    have hQ : Bundle bolt (marks G c r) (native c) a a (Q-L₀) B n d (M*δ) := Polar.toBundle h.covarianceJets (h₁.trans he)
    have hX := hL.multiply hQ (Mark.position_move _ _ hr.le) hr.le le_rfl hm (mul_nonneg hm hb) hr.le (ht ▸ he : r+n*r ≤ d)
    refine (hX.mono le_rfl (le_of_eq ?_)).glue ?_
    · unfold M₁ FreeResolvent.tagPrice; ring
    · filter_upwards [germ_valid (A:=L) (h.solvency.shift 0 |>.unit_det (show 0<η+0 by positivity))
          h.gramJets.smooth.continuousAt] with y hy
      unfold Neat at hy; rw [zero_smul,add_zero] at hy
      change L y * (Q y-(L y)⁻¹) = _
      rw [Matrix.mul_sub,Matrix.mul_nonsing_inv _ hy]
  have hM₁ : 0 ≤ M₁ := by unfold M₁ FreeResolvent.tagPrice; positivity
  refine ⟨thin hV le_rfl h₂ le_rfl,?_⟩
  have hP := (h.cov_inverse p hp le_rfl).polar p.meter_abs (show 0 ≤ (0:ℝ) from le_rfl)
  rw [shift_zero,show drain 0=1 by simp [drain],mul_one] at hP
  have hX := (Polar.toBundle hV h₂).multiply ((Polar.toBundle (show Polar B a a Q₀ n σ C from hP)
    (h₂.trans h₁)).mono h₁ le_rfl) (Mark.position_move _ _ h₀.le) h₀.le le_rfl
    (mul_nonneg hM₁ hb) p.meter_abs h₀.le hw.le
  refine (((hX.scale (-1)).mono le_rfl (le_of_eq ?_)).glue ?_)
  · unfold M₂ C M₁ FreeResolvent.tagPrice; rw [abs_neg,abs_one]; ring
  · filter_upwards [germ_valid (A:=Q) (h.covSanction.shift 0 |>.unit_det (show 0<l+0 by linarith only [p.r0]))
      h.cJets.smooth.continuousAt] with y hy
    unfold Neat at hy; rw [zero_smul,add_zero] at hy
    change (-1:ℝ) • ((L y*Q y-1)*(Q y)⁻¹)=(Q y)⁻¹-L y
    rw [Matrix.sub_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hy, Matrix.mul_one,Matrix.one_mul]
    simp
end extendCost

/-- Deliver residual kernel bounds for the actual affine quadratic correction
(no `PointCharge` of the supplied rough pre-Gaussian values used in their
place). Shrunk widths; everything simultaneous. -/
structure Estimate (n : ℕ) (d v η lower M : ℝ) (A : Stores S) (F : Forest S.ratio) (T : Tube G S)
    (x : ℝ) (V : Config G c) (k : S.Choices) (B : PriceCoords G c) : Prop
    extends KernelJets n d v η lower M A F T x V k B where
  covarianceInverse : ∀ u : ℝ, 0 ≤ u → ResolventJets (Wisps.front A F) B n d M u
    (action (pickedCov A F T x V k) u)
  sJets : Polar B (Wisps.front A F) (Wisps.front A F) (pickedS A F T x V k) n d (M * Real.exp (-v*radiusB x))
  inverseGapJets : Polar B (Wisps.front A F) (Wisps.front A F) (pickedDelta A F T x V k) n d
    (M * Real.exp (-v*radiusB x))

theorem estimates (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r d v η l M : ℝ, 0<r ∧ 0<d ∧ 0<v ∧ 0<η ∧ 0<l ∧ 0<M ∧
    ∀ᶠ x : ℝ in atTop, 120 ≤ radiusB x ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (k : S.Choices) (B : PriceCoords G c), ‖B‖≤r →
      Estimate n d v η l M A F T x V k B := by
  obtain ⟨r,d,v,η,l,M,hr,hd,hv,hη,hl,hM,H⟩ := assembly G P Pt hk n
  let t := room d M l n; have ht : 0<t := (room_grid hd hM.le hl n).1
  let s : ℝ := t/(n+1:ℕ)^2; have hs : 0<s := by unfold s; positivity
  let X := priceFiber P G t; let Q : Price d M l t 1 X 1 n :=
    ⟨hl,hM.le,hd,rfl,le_rfl,(priceFiber_pos ..).le,zero_le_one,le_rfl⟩
  let D := meter n n M 1 (rise X l); have hD : 0 ≤ D := Q.meter_abs
  let M₁ := FreeResolvent.tagPrice 1 n M M; have h₁ : 0 ≤ M₁ := by unfold M₁ FreeResolvent.tagPrice; positivity
  let M₂ := FreeResolvent.tagPrice 1 n M₁ D; have h₂ : 0 ≤ M₂ := by unfold M₂ FreeResolvent.tagPrice; positivity
  let C := M + D + M₁ + M₂
  have hc : M ≤ C := by unfold C; linarith only [hD,h₁,h₂]
  have hy : s ≤ t := by
    unfold s; apply div_le_self ht.le
    apply one_le_pow₀
    push_cast; simp
  refine ⟨r,s,v,η,l,C,hr,hs,hv,hη,hl,hM.trans_le hc,?_⟩
  filter_upwards [H] with x hx
  obtain ⟨he,H⟩ := hx
  refine ⟨he,?_⟩
  intro c f S T hP hF hp A F V hA k B hB
  have he := H S T hP hF hp A F V hA k B hB
  have hX : (native c).Volume (Wisps.front A F (x:=x) (G:=G)) t X := by
    rw [show X = priceFiber S.patch G t from by unfold X; rw [hP]]; exact (fiber_volume S G ht A F x).1
  obtain ⟨hj,hg⟩ := he.funds_small Q hη hX
  exact { he.costs hc (hy.trans (room_small Q)) with
          covarianceInverse := fun u hu => (he.cov_inverse Q hX hu).weaker le_rfl
            (show D ≤ C by unfold C; linarith only [hM,h₁,h₂]) hy hu
          sJets := thin hj le_rfl le_rfl (mul_le_mul_of_nonneg_right (show M₁≤C by unfold C; linarith only [hM,hD,h₂]) (Real.exp_pos _).le)
          inverseGapJets := thin hg le_rfl le_rfl (mul_le_mul_of_nonneg_right
            (show M₂ ≤ C by unfold C; linarith only [hM,hD,h₁]) (Real.exp_pos _).le) }
end YM.AnalyticBridge.SectorAffine
