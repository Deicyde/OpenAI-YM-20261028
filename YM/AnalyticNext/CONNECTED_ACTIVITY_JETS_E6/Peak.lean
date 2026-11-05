import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mean

/-!
# Rare complements really require Gaussian-scale excursions

Default profiles in physical config (all orientations and predictors use same
V). Applies already on processed letters, does NOT assume all other gamma's or
defaults still intact. Tree accounting can therefore charge one transition hit
per witness; gather them in one probability expectation on the sector. Pre L
mark conditions separated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

lemma tiny_flame (G : Gauge) (L : Side) {E : ℝ → ℝ} (h : Rate G L (-1) E) {k : ℝ} (hk : 0 < k) :
    ∀ᶠ x : ℝ in atTop, E x ≤ k*Pressure.fiery G x L := by
  let H x := betaF G x L
  have hx : Rate G L (-1+(1/2:ℝ)) (fun x => E x* H x^(1/2:ℝ)) := h.mul Rate.power
  filter_upwards [hx.below (by norm_num) k hk,Delay.shift_pos G L] with x hv hy
  let s := Real.sqrt (betaF G x L)
  have ht : s>0 := Real.sqrt_pos.mpr hy
  have hg : E x*s ≤ k := by rw [show s=H x^(1/2:ℝ) from Real.sqrt_eq_rpow _]; exact (le_abs_self _).trans hv
  have he : 1 ≤ Delay.fineMonitor G L x := Real.one_le_exp (sq_nonneg _)
  apply le_trans ((le_div_iff₀ ht).2 hg) _; rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_right (inv_nonneg.mpr ht.le) he) hk.le

namespace Coat
abbrev Air (f : Side) (G : Gauge) := EuclideanSpace ℝ (Tubular f G)

variable (X : Coat T F)
def gStep (β : ℝ) := (Real.sqrt β)⁻¹

def atmos (_X : Coat T F) (z : Air f G) := erect G (WithLp.ofLp z)
def liftA (β : ℝ) (z : Air f G) := X.μ + gStep β • X.atmos z

def watch (x : Site c) (ξ β : ℝ) (B : ℕ) (z : Air f G) :=
    ∀ i : Tubular f G, separation x (along S i) ≤ B → |z i| ≤ ξ*X.t*(gStep β)⁻¹

lemma watch_bonds (x : Site c) {ξ β M : ℝ} {B : ℕ} {z : Air f G} (hp : 0<X.t) (hξ : 0≤ξ) (hβ : 0<β)
    (he : X.watch x ξ β B z) (i : Bond f) (h : separation x (atEdge S i) ≤ B) (hm : ‖X.μ i‖ ≤ M*X.t) :
    ‖X.liftA β z i-X.μ i‖≤(Fintype.card G.ColorIndex)* (ξ*X.t) ∧
      ‖X.liftA β z i‖ ≤ (M+Fintype.card G.ColorIndex*ξ)*X.t := by
  have hg : 0<gStep β := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have ht : ‖gStep β • X.atmos z i‖ ≤ (Fintype.card G.ColorIndex)* (ξ*X.t) := by
    refine color_cover (mul_nonneg hξ hp.le) _ (fun j => ?_)
    rw [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hg]
    exact (mul_le_mul_of_nonneg_left (he (i,j) h) hg.le).trans_eq (by field_simp)
  simp only [liftA,Pi.add_apply,Pi.smul_apply,add_sub_cancel_left]
  exact ⟨ht,(norm_add_le _ _).trans ((add_le_add hm ht).trans_eq (by ring))⟩

lemma canon_reply (h : P.Funds S T) (p : Rod c f) (u : Directions G f) : X.realPath 1 p u= reply T X.x X.V X.k (X.signal u) p := by
  unfold realPath; rw [SliceRows.turns_here,pull_id]
  have hk := (carry 1 (funds_branch h) X.k (replica S.ratio X.V)).2; simp only [pull_id] at hk
  unfold reply request baseStroke entryCost; rw [hk]

/-- Pick quotas ready for both predictor and fine plateau. -/
structure Goals (P : Teller G) (A W τ : ℝ) (L : Side) : Prop where
  A_pos : 0<A
  W_pos : 0<W
  limit : 0<τ
  fine : (2/Real.sqrt P.top.clip.direct)*(A/(L.val:ℝ)^2+τ) < 1/4
  noise : (2/Real.sqrt P.bind.penalty)*(A+τ) < W

/-- Possible with genuine pre-L maximum and every W≥ post. -/
lemma scopes (P : Teller G) (A : ℝ) (hA : 0<A) : ∃ τ : ℝ, 0<τ ∧ ∃ L₀ : ℕ, ∀ L : Side, L₀ ≤ L.val →
    ∀ᶠ W : ℝ in atTop, Goals P A W τ L := by
  let τ := Real.sqrt P.top.clip.direct/32
  have ht : 0< Real.sqrt P.top.clip.direct := Real.sqrt_pos.mpr P.top.clip.quadratic_pos
  have hτ : 0 < τ := by unfold τ; positivity
  obtain ⟨n,hn⟩ := exists_nat_gt (A/τ)
  refine ⟨τ,hτ,n,fun L hL => ?_⟩
  let b := 2/Real.sqrt P.bind.penalty
  filter_upwards [eventually_gt_atTop (b*(A+τ)),eventually_gt_atTop (0:ℝ)] with W hh h
  refine ⟨hA,h,hτ,?_,hh⟩
  have he : 1 ≤ (L.val:ℝ) := by exact_mod_cast L.property
  have hg : A/τ < L.val := lt_of_lt_of_le hn (by exact_mod_cast hL)
  rw [div_mul_eq_mul_div, div_lt_iff₀ ht]
  have ha : A/(L.val:ℝ)^2 ≤ τ := by
    refine (div_le_iff₀ (by positivity)).mpr ?_; nlinarith [(div_lt_iff₀ hτ).mp hg]
  unfold τ at *; linarith

/-- Does NOT need V predictor or U actual flag *far*: the row on
unclipped F is a test of all μ-protected profiles. k may be chosen
arbitrarily; use k' from channel 1 in cost (choices may permute; use
prediction equality). -/
theorem ready (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) {A W τ : ℝ} (ht : Goals P A W τ L)
    {η r Q Y M : ℝ} (ho : Torch η r Q) : ∃ ξ : ℝ, 0 < ξ ∧ Fintype.card G.ColorIndex * ξ ≤ 1 ∧
    ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F),
      X.x=x → S.patch=D → S.patch.L=L → Rotator P L η r Q Y X → Stamp T → X.manifest →
      (∀ i, ‖X.μ i‖ ≤ M*X.t) → 0<M → Maximum A T X.x X.V → ∀ o : Site c, ¬Inside o X.seeds (30*X.B) →
      ∀ β>0,∀ z : Air f G, X.watch o ξ β X.B z → let v := X.liftA β z; let U:=X.input v
      Tags.siteMass U X.k o=1 ∧ (∀ p : Cell f, S.ratio.parent p.1=o → toll U p < X.t/4) ∧
        ∀ i : Axis, Tags.pinMass U X.k (o,i)=1 ∧ wire (S.prediction U X.k) X.V (o,i) < W*X.t := by
  let c₀ := (Fintype.card G.ColorIndex:ℝ)
  have hτ := ht.limit
  have hO : 0≤ c₀ := Nat.cast_nonneg _
  let f := c₀*(scale⁻¹*|Y|)*3
  let ξ := min (c₀+1)⁻¹ (τ/(f+1))
  have hs := Coat.scale_pos
  have hf : 0≤f := by unfold f; positivity
  have hξ : 0<ξ := by unfold ξ; exact lt_min (by positivity) (by positivity)
  have he : c₀*ξ≤1 := by
    calc
      _ ≤ c₀*(c₀+1)⁻¹ := mul_le_mul_of_nonneg_left (min_le_left ..) hO
      _ ≤ _ := by rw [← div_eq_mul_inv]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hp : c₀*(scale⁻¹*(Y*ξ)) ≤ τ/3 := by
    have hp := (le_div_iff₀ (show 0<f+1 by linarith)).mp (show ξ≤τ/(f+1) from min_le_right ..)
    have he : Y*ξ≤|Y| *ξ := mul_le_mul_of_nonneg_right (le_abs_self _) hξ.le
    unfold f at *; nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hs.le)) hO]
  refine ⟨ξ,hξ,he,?_⟩
  obtain ⟨B,δ,hB,hδ,h⟩ := Work.E05.curvature_lower G
  let Z x := (|M|+c₀*ξ)*Pressure.fiery G x L  -- actual upper M positive consumer
  have hv : Rate G L (-(1/2)) Z := Rate.flame.mul_left _
  have hz : ∀ᶠ x in atTop,0 ≤ Z x := Eventually.of_forall fun x => by unfold Z Pressure.fiery Pressure.temp; positivity
  obtain ⟨N,H,hN,hH,hx⟩ := strokes P L D hd hv hz
  obtain ⟨E,hE,hG⟩ := pressure_mean P D hd L η r Q Y ho
  filter_upwards [marks_here P L D hd hv hz δ hδ,hG, hx, hz,
    tiny_flame G L hE (show 0<τ/3 by linarith), tiny_flame G L hH (show 0<τ/3 by linarith)] with
    x hy HG hu hw hf' hh c f S T F X hX hS hL hr hs' he' hU hM hV o hx β hβ z hk v U
  subst x
  have hP := hr.room
  have H₀ : 0<X.t := hr.room.fiery
  have hd : 100 ≤ X.B := hP.sight.1
  have hY : Clean X.V X.x o X.B := (clean_far X.seeds X.V he' hx).shrink (v:=o) (by rw [separation_self]; omega)
  have ht' : Grafted X.V U (X.signal v) o (X.B/2) (Z X.x) S := by
    refine (X.distant v o hw (fun h => hx (Corona.halo_mono (by omega) (Finset.Subset.refl _) h))
      (fun i hi _ => ?_)).less (by rw [separation_self, zero_add]; omega)
    unfold Z; rw [abs_of_pos hM,← hL]; exact (X.watch_bonds o H₀ hξ.le hβ hk i hi (hU i)).2
  obtain ⟨HE,H₁,H₂⟩ := hy c f S T hS hL hP U X.k X.V o (X.signal v) hY ht'
  have hK := (HG c f S T hS hL hs' F X rfl hr he').2
  have hv0 p (hb : focus S p=o) : root S (1,p)=o := by simp [root,hb]
  have htick p (hh' : focus S p=o) : ‖bill T X.x U X.k X.V p‖ ≤ τ*X.t := by
    let w : Mention c f := (1,p)
    have hs : X.selected w.1 (spot S w.2) := by
      unfold selected addr; rw [← cost_is_here]
      change ¬Inside (root S (1,p)) _ _; rw [hv0 p hh']; exact fun h => hx (Corona.halo_mono (by omega) (Finset.Subset.refl _) h)
    have hE := hK w ((hv0 p hh').symm ▸ hx)
    have ht := (hu.2.2 c f S T hS hL hP U X.k X.V p (X.signal v) (hh'.symm ▸ hY) (hh'.symm ▸ ht')).2
    have hξ' : 0 ≤ ξ*X.t := by positivity
    have h₂ := X.hips v X.μ w hs hξ' hr (fun i hi => by
      let g := gStep β; have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
      change |X.μ i.1 i.2 + g * z i - X.μ i.1 i.2| ≤ ξ*X.t
      rw [add_sub_cancel_left,abs_mul,abs_of_pos hg]
      apply (mul_le_mul_of_nonneg_left (hk i (by rw [← hv0 p hh']; exact hi)) hg.le).trans_eq
      change g*(ξ*X.t*g⁻¹)=_; field_simp)
    let C : G.Color := bill T X.x U X.k X.V p
    have h : ‖C-X.realPath w.1 w.2 v‖ ≤ H X.x := by rw [X.canon_reply hP.accepted]; exact accuracy2 _ ht
    have h' := (norm_sub_le_norm_sub_add_norm_sub C (X.realPath w.1 w.2 v) 0)
    have h₃ := norm_sub_le_norm_sub_add_norm_sub (X.realPath w.1 w.2 v) (X.realPath w.1 w.2 X.μ) 0
    rw [sub_zero,sub_zero] at h' h₃
    change ‖C‖ ≤ _
    rw [← hL] at hf' hh; change _ ≤ _*X.t at hf' hh
    unfold c₀ at *; linarith only [h,h',h₂,h₃,hE,hf',hh,mul_le_mul_of_nonneg_right hp H₀.le]
  have ho' := ht.A_pos
  refine ⟨HE, fun p hb => ?_,fun i => ⟨(H₁ i).1,?_⟩⟩
  · obtain ⟨h1,h2⟩ := h _ (H₂ p hb.symm)
    let p' : Rod c f := .inl (p,false)
    let C' := A/(L.val:ℝ)^2+τ
    have hc : 0≤ C'*X.t := by unfold C'; positivity
    have hp : ‖entryCost T X.R U X.k X.V p'‖ ≤ C'*X.t := calc
      _ ≤ ‖bill T X.x U X.k X.V p'‖+‖guide T X.x X.V p'‖ := by
        simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub _ (guide T X.x X.V p') 0
      _ ≤ _ := by
        have he := hV.phi (p,false)
        have hx : ‖guide T X.x X.V p'‖ ≤ A/(L.val:ℝ)^2*X.t := by rw [← hL]; exact he
        unfold C'; linarith [htick p' hb]
    change ‖Real.sqrt T.high.direct • G.curvature (faceValue U p)‖ ≤ _ at hp
    rw [hP.accepted.high] at hp
    apply lt_of_le_of_lt (sqrt_compare P.top.clip.quadratic_pos hc _ h2 hp)
    rw [← mul_assoc]; have hx := mul_lt_mul_of_pos_right ht.fine H₀; linarith
  let p' := (o,i); let r : Rod c f := .inr p'
  have hE := (H₁ i).2
  obtain ⟨hz,hv⟩ := h _ hE
  have hc : ‖entryCost T X.R U X.k X.V r‖ ≤ (A+τ)*X.t := calc
    _ ≤ ‖bill T X.x U X.k X.V r‖+‖guide T X.x X.V r‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub _ (guide T X.x X.V r) 0
    _ ≤ _ := by
      have hp := paysGuide r (T:=T) ht.A_pos.le X.V hV
      linarith [htick r rfl]
  change ‖Real.sqrt S.kernel.penalty • G.curvature _‖ ≤ _ at hc; rw [hP.accepted.knobs] at hc
  refine lt_of_le_of_lt (sqrt_compare P.bind.penalty_pos (show 0≤ (A+τ)*X.t by positivity) _ hv hc) ?_
  rw [← mul_assoc]; exact mul_lt_mul_of_pos_right ht.noise H₀
end Coat
end YM.ConnectedActivityE6
