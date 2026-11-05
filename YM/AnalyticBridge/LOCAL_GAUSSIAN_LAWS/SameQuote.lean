import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Accuracy
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Geometry
import YM.Next.FREE_KERNELS.Sell
import YM.Next.ROTATIONS.Dyad
import YM.Push.FREE_RESOLVENT.Masking
import YM.Push.FREE_RESOLVENT.SharedCells
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.ResidualPrice



/-!
# Weighted comparison, purchased once at the actual cut selected A

Translate `opaqueCost` into both APIs. Price the actual *alternative*
Midpoint table and ordered mean operator, simultaneously with fog,
including changes of window and associated precision and logdet errors.
After-L only. Refund no volume factors: the log of the determinant ratio
has a dimension, useful also if comparing local marginals/windows
separately. This isn't the separate RELATIVE_LOGDET_TRACE (uses
ResidualPrice.local_log, no log chains, no support bookkeeping), ordered
derivative or LOCAL_GAUSSIAN_MULTIPLIER task. No claim on determinant of
active A vs flat no-hole A (where a naive exchange even of dimensions
would fail). Actual Gaussian change formula itself follows separately.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Next SectorChange Function Set Matrix FreeResolvent Filter
open scoped Classical BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] {D : Cost ι}

/-- Bound on the scalar part of change-to-Q for covariance C.
`log (det C)+log (det Q) = log (det(Q*C))`. -/
lemma log_payment {X : Type} {D : Cost X} {a : ι → X} {s δ : ℝ}
    {Q C : Matrix ι ι ℝ} (hQ : Q.PosDef) (hC : C.PosDef) (hs : 0 ≤ s)
    (hδ : 0 ≤ δ) (he : δ ≤ 1/2) (hr : D.Schur a a s δ (Q*C-1)) :
    |Real.log (C.det) + Real.log (Q.det)| ≤ Fintype.card ι*(2*δ) := by
  let A := Q*C
  have hx : A.det=Q.det*C.det := Matrix.det_mul ..
  have h : A.det > 0 := hx ▸ mul_pos hQ.det_pos hC.det_pos
  have ho i := (hr.mono hs le_rfl).cols.bound i
  simp only [Cost.weight_zero,one_mul,Matrix.transpose_apply] at ho
  have hh := ResidualPrice.local_log (Q:=A-1) (A:=A) ho (show A=1+(A-1) from (by abel)) h hδ he
  rwa [hx,mul_comm,Real.log_mul hC.det_pos.ne' hQ.det_pos.ne'] at hh

structure Closes {X : Type} (D : Cost X) (a : ι → X) (Q : Gaussian.Table ι)
    (W : ι → Set ι) (s M η C e gap : ℝ) : Prop where
  -- Q and associated scaled inverse
  lower : FreeResolvent.Gap Q η
  pays : D.Schur a a s M Q
  primal : Q.PosDef
  -- include all u for primary window & E formula
  issuer (u : ℝ) (hu : 0 ≤ u) :
    let P := pane W Q u
    D.Schur a a s (C*(1+u)⁻¹) P ∧ D.Schur a a s (C*(1+u)⁻¹) (resolve Q u) ∧
      D.Schur a a s (M*e*(1+u)⁻¹) ((Q+u • 1)*P-1) ∧
        D.Schur a a s (e*((1+u)⁻¹)^2) (P-resolve Q u)
  gap_cov : FreeResolvent.Gap (mirror (pane W Q 0)) gap
  cloud : (mirror (pane W Q 0)).PosDef
  compares :
    let Z := mirror (pane W Q 0)
    D.Schur a a s C Z ∧ D.Schur a a s e (Z-Q⁻¹) ∧ D.Schur a a s (M*e) (Q*Z-1) ∧
      D.Schur a a s (2*M^2*e) (Z⁻¹-Q) ∧ D.Schur a a s (2*M) Z⁻¹ ∧
      |Real.log Z.det + Real.log Q.det| ≤ Fintype.card ι*(2*M*e)

/-- Choice of V from the application. Monotone form (allow a larger M,
C than one actually needed, so no issues collecting quotes). -/
theorem closes_of_fine {X : Type} {D : Cost X} {a : ι → X} {W : ι → Set ι} {Q : Gaussian.Table ι} {s M η V μ γ R M' C e : ℝ}
    (H : Margin W Q D a s M η V μ γ R) (hQ : Q.IsSymm) (hm : M ≤ M') (hm' : 1 ≤ M')
    (hc : stampFee V η ≤ C) (hc' : 1 ≤ C)
    (hf : Real.exp (-(μ-γ)*R)*(M'*C^2) ≤ e)
    (he : e < η/(M+1)^2/2) (hd : M'*e ≤ 1/2) :
    Closes D a Q W γ M' η C e (η/(M+1)^2/2) := by
  let θ := Real.exp (-(μ-γ)*R)
  let C₀ := stampFee V η; let δ := θ*(M*C₀^2)
  have hv : 0 ≤ θ := (Real.exp_pos _).le
  have hl := H.upper; have hy : 0 ≤ M' := zero_le_one.trans hm'
  have hx : 0 ≤ C₀ := stampFee_nn H.bulk H.lower
  have hδ : 0 ≤ δ := by unfold δ; positivity
  have ha : δ ≤ e := (show δ ≤ θ*(M'*C^2) from (by unfold δ; gcongr)).trans hf
  have hp := hδ.trans ha
  have hh : M*δ ≤ 1/2 := (mul_le_mul hm ha hδ hy).trans hd
  obtain ⟨hP,hZ,hG,h0,h1,h2,h3⟩ := covariance H hQ (ha.trans_lt he) hh
  let Z := mirror (pane W Q 0)
  have hr : D.Schur a a γ (M'*e) (Q*Z-1) :=
    h3.mono le_rfl (mul_le_mul hm ha hδ hy)
  have hb : D.Schur a a γ (2*M'^2*e) (Z⁻¹-Q) := h2.mono le_rfl (by gcongr)
  have ht : |Real.log Z.det + Real.log Q.det| ≤ Fintype.card ι * (2*M'*e) := by
    rw [mul_assoc 2]
    exact log_payment hP hZ H.rates.1.le (mul_nonneg hy hp) hd hr
  have hw := H.income.mono (H.rates.2.1.le.trans H.rates.2.2) hm
  refine ⟨H.gap,hw,hP,?_,hG,hZ,h0.mono H.rates.2.1.le hc,
    (show D.Schur a a γ e (Z-Q⁻¹) from (by rw [show Q⁻¹=resolve Q 0 from (by unfold resolve; simp)]; exact h1.mono le_rfl ha)),hr,hb,?_,ht⟩
  · intro u hu P
    obtain ⟨h, h', h'', h'''⟩ := fine H hu
    have hv' : 0 ≤ (1+u)⁻¹ := by positivity
    refine ⟨h.mono H.rates.2.1.le (by gcongr),h'.mono H.rates.2.1.le (by gcongr),h''.mono le_rfl ?_,h'''.mono le_rfl (by gcongr)⟩
    apply mul_le_mul_of_nonneg_right _ hv'
    have hi : C₀ ≤ C^2 := hc.trans (by nlinarith)
    calc
      θ*(M*C₀) ≤ θ*(M'*C^2) := by gcongr
      _ ≤ e := hf
      _ ≤ M'*e := le_mul_of_one_le_left hp hm'
  rw [show Z⁻¹=Z⁻¹-Q+Q from (by abel)]
  refine (hb.add hw).mono le_rfl ?_
  nlinarith only [mul_le_mul_of_nonneg_left hd hy]

/-- Direct comparison between the two purchased clouds. u estimates can
be added in the same fashion, we only price the density substitution's
ordered and symmetrized ops here. -/
theorem switchPrice {X : Type} {D : Cost X} {a : ι → X} {Q : Gaussian.Table ι}
    {W H : ι → Set ι} {s M η C e g : ℝ}
    (hW : Closes D a Q W s M η C e g) (hH : Closes D a Q H s M η C e g) :
    let Y := pane W Q 0; let Z := pane H Q 0
    let F := mirror Y; let F' := mirror Z
    D.Schur a a s (2*e) (Y-Z) ∧ D.Schur a a s (2*e) (F-F') ∧
      D.Schur a a s (4*M^2*e) (F⁻¹-F'⁻¹) ∧
      |Real.log (F.det/F'.det)| ≤ Fintype.card ι*(4*M*e) := by
  intro Y Z F F'
  obtain ⟨-,-,-,hY⟩ := hW.issuer 0 le_rfl
  obtain ⟨-,-,-,hZ⟩ := hH.issuer 0 le_rfl
  simp only [add_zero, inv_one, one_pow,mul_one] at hY hZ
  have ha : D.Schur a a s (2*e) (Y-Z) := by
    rw [show Y-Z=(Y-resolve Q 0)-(Z-resolve Q 0) from (by abel)]
    exact (hY.sub hZ).mono le_rfl (le_of_eq (by ring))
  obtain ⟨-, -, -, hb,-, hl⟩ := hW.compares; obtain ⟨-, -, -, hc,-, hk⟩ := hH.compares
  have ht : |Real.log (F.det/F'.det)| ≤ Fintype.card ι*(4*M*e) := by
    rw [Real.log_div hW.cloud.det_pos.ne' hH.cloud.det_pos.ne']
    have he (x y z : ℝ) : x-y=x+z-(y+z) := by ring
    rw [he _ _ (Real.log Q.det)]; exact (abs_sub ..).trans ((add_le_add hl hk).trans_eq (by ring))
  refine ⟨ha,?_,?_,ht⟩
  · unfold F F'; rw [← mirror_sub]; exact mirrored ha
  rw [show F⁻¹-F'⁻¹=(F⁻¹-Q)-(F'⁻¹-Q) from (by abel)]
  exact (hb.sub hc).mono le_rfl (le_of_eq (by ring))

section named
open Lattice Wilson Exterior Precision RG Pressure Pressure.Stores Rows Tree Bid Wisps

/-- Volume receipt for **any** Active system and locations (*not* on
identified sites deleting multiplicities). -/
lemma mass_front {G : Gauge} {c f : Side} {S : StepData c f} (A : Stores S) (F : Forest S.ratio) (x : ℝ) {σ : ℝ}
    (hs : 0<σ) :
    (native c).Volume (front A F (G:=G) (x:=x)) σ (torusPay (Bloch.Co S.patch.L (PAC G 1)) σ) :=
  (FreeResolvent.Affine.home_volume (G:=G) S 1 σ hs).comp (register A F x G).injective

/-- All-radius applications after delay for chosen P,L. No global fine
config realizing Σ needed. Simultaneous for every set family at this
parent-ball radius (incl identity completion if chosen at those same
centers). Gives actual midpoint version, and *between* the two windows,
not just a grant condition. hD must still be incorporated into prices in
order (can just take eventually on each L) rather than imposed on an
arbitrary past Directed step. -/
theorem common_cover (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G) :
    ∃ η σ M C E g : ℝ, 0 < η ∧ 0 < σ ∧ 1 ≤ M ∧ 1 ≤ C ∧ 0 < E ∧ 0 < g ∧
    ∀ᶠ x : ℝ in atTop,
      let e := E * Real.exp (-σ * (radiusB x:ℝ))
      M*e ≤ 1/2 ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
        S.patch=P → 100*(1+radiusB x)≤c.val → Pt.Funds S T →
          ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c),
            A.flags=RG.flags (temp x) V →
            ∀ U : In x A F (G:=G) → Set (In x A F (G:=G)),
              SectorChange.Schur.Bars U (front A F) (radiusB x/60) →
                Closes (native c) (front A F) (Rows.gram T x V k (shots S x) A F) U σ M η C e g := by
  obtain ⟨s,H,η,b,K,hs,hH,hη,-,-,hq⟩ := opaqueCost G P Pt h
  let v := safeRate s H η
  let a := v/2; let n := v/240 -- s retained in exponential Schur on output
  let m := v-a
  let Y := torusPay (Bloch.Co P.L (PAC G 1)) m
  let M := max 1 H
  let D := max 1 (stampFee Y η)
  let E := M*D^2
  let δ := η/(H+1)^2/2
  have hv : 0<v := FreeResolvent.rate_pos hs hH hη
  have hn : 0<n := by unfold n; positivity
  have ha : n < a := by unfold n a; linarith
  have hw : a ≤ s := (half_le_self hv.le).trans (rate_lt hs).le
  have hm : 0<m := by unfold m a; linarith
  have hY : 0≤Y := torusPay_nn _ _ hm
  have hM : 1 ≤ M := le_max_left ..
  have hD : 1 ≤ D := le_max_left ..
  have hE : 0 < E := mul_pos (by linarith) (pow_pos (by linarith) _)
  have hδ : 0 < δ := by unfold δ; positivity
  let F (x : ℝ) := E * Real.exp (-n * (radiusB x))
  have he : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun x : ℝ => Real.exp (-n*(radiusB x))) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
      ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp Work.E01.radiusB_tendsto) |>.const_mul_atTop_of_neg (neg_lt_zero.mpr hn))
    simpa only [mul_zero,F] using! hi.const_mul E
  have he' : Tendsto (fun x => M * F x) atTop (𝓝 0) := by simpa only [mul_zero] using! he.const_mul M
  -- a-n >= 119n, to cover B/60 including integer floor
  refine ⟨η,n,M,D,E,δ,hη,hn,hM,hD,hE,hδ,?_⟩
  filter_upwards [hq,he.eventually (gt_mem_nhds hδ), he'.eventually (gt_mem_nhds (half_pos zero_lt_one)), Work.E01.radiusB_tendsto.eventually_ge_atTop 180] with x hA h₀ h₁ h₂
  intro e
  refine ⟨h₁.le,?_⟩
  intro c f S T hS hl hp A I k V hV U ht
  obtain ⟨hQ,hg,-⟩ := hA S T hS hl hp A I k V hV
  let Q := Rows.gram T x V k (shots S x) A I
  let r : ℕ := radiusB x /60
  have hr : Margin U Q (native c) (front A I) s H η Y a n r := by
    refine ⟨(pours_iff.mp hQ).2,gapped_iff.mp hg,hs,hH,hη,hY,?_,⟨hn,ha,hw⟩,bars_hasCenters ht,bars_near ht⟩
    have h' : (native c).Volume (front A I (G:=G) (x:=x)) m Y := by unfold Y; rw [← hS]; exact mass_front A I x hm
    exact h'
  apply closes_of_fine hr ?_ (le_max_right ..) hM (le_max_right ..) hD ?_ h₀ h₁.le
  · unfold Q Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  change Real.exp (-(a-n) * r) * E ≤ E * _
  rw [mul_comm E]; apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) hE.le
  have hx : radiusB x ≤ 119*r := by unfold r; omega
  have hx' : (radiusB x:ℝ) ≤ 119*(r:ℝ) := by exact_mod_cast hx
  unfold a n; nlinarith only [mul_le_mul_of_nonneg_left hx' hv.le]

/-- Both naked actual ordered kernels and their real probability
covariances at the *same* Gram, incl full switched exponent ingredients.
No claims of dispatch on an already Paid Directed unless waits so booked.
Raw flags are compared as inputs--not differentiated. -/
theorem quote (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G) :
    ∃ η σ M C E g : ℝ, 0 < η ∧ 0 < σ ∧ 1 ≤ M ∧ 1 ≤ C ∧ 0 < E ∧ 0 < g ∧
    ∀ᶠ x : ℝ in atTop,
      let e := E * Real.exp (-σ * (radiusB x:ℝ))
      M*e ≤ 1/2 ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
        S.patch=P → 100*(1+radiusB x)≤c.val → Pt.Funds S T →
          ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c),
            A.flags=RG.flags (temp x) V →
            let H (U) := Closes (native c) (front A F) (Rows.gram T x V k (shots S x) A F) U σ M η C e g
            H (panels A F) ∧ H (midSets S (radiusB x) A F x G) := by
  obtain ⟨η,σ,M,C,E,g,hη,hh,hm,hc,he,hg,h⟩ := common_cover G P Pt h
  refine ⟨η,σ,M,C,E,g,hη,hh,hm,hc,he,hg,?_⟩
  filter_upwards [h,Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hx hp
  intro e; refine ⟨hx.1,?_⟩; intro c f S T hs hl ht A F k V hV H
  have h := hx.2 S T hs hl ht A F k V hV
  obtain ⟨hy,hz⟩ := both_bars S hp A F x G
  exact ⟨h _ hz,h _ hy⟩
end named
end YM.AnalyticBridge.LocalGaussianLaws
