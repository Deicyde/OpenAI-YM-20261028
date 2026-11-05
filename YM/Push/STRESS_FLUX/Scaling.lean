import YM.Push.STRESS_FLUX.Annihilator
import YM.Push.STRESS_FLUX.Annular
import YM.Work.A05.Window


/-! From paid annular nodes to arbitrary finite lists of annular tests in the
continuum. We integrate the *annihilators*, not any family of arbitrarily
chosen node-wise counterterms. Generic point passage suffices. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Annular
open Matching Table Work.A01 Work.A05 Analysis MeasureTheory Function Filter Set
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {i d h D m n : ℕ} {r ε : ℝ} {V : E4 → E4} {W : DiffPlan S} {H : S.RealSpin}

structure Motion (j : ℕ) (V : E4 → E4) : Prop where
  smooth : ∀ b : Axis, ContDiff ℝ ∞ fun z => V z b
  rigid : killing V
  scales (r : ℝ) (hr : 0<r) (z : E4) : V (r • z) = (r^j) • V z

def cutoff : ContDiffBump (0:E4) := ⟨1/2,1,by norm_num,by norm_num⟩

lemma weight_off (a : Axis) (b : E4 → ℝ) {z : E4} (hz : Work.A05.weight cutoff a b z ≠ 0) : 1/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 := by
  have he : z ∈ tsupport (fderiv ℝ (cutoff : E4 → ℝ)) := subset_closure (show fderiv ℝ (cutoff : E4 → ℝ) z ≠ 0 from fun h => hz (by simp [Work.A05.weight,Analysis.D,h]))
  have ht := tsupport_fderiv_subset ℝ he; rw [cutoff.tsupport_eq] at ht
  refine ⟨?_, by simpa [Metric.mem_closedBall,dist_zero_right,cutoff] using ht⟩
  by_contra! h
  apply notMem_tsupport_iff_eventuallyEq.mpr _ he
  have hz : z∈ Metric.ball (0:E4) cutoff.rIn := by simp only [Metric.mem_ball,dist_zero_right,cutoff]; linarith
  have hh : (cutoff : E4 → ℝ) =ᶠ[𝓝 z] fun _ => 1 := (Metric.isOpen_ball.eventually_mem hz).mono fun _ hu => cutoff.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
  simpa using hh.fderiv (𝕜:=ℝ)

lemma eventual_stretch (s : Audience L) {e : ℕ → ℝ} (hp : ∀ k, 0 < e k) (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ k : ℕ in atTop, Window s.x (stretch (e k) cutoff) := by
  have hu (i : Fin s.n) : ∀ᶠ k in atTop, ((e k)⁻¹ • s.x) i.succ ∉ tsupport (cutoff : E4 → ℝ) := by
    have hr : 0 < ‖s.x i.succ‖ := norm_pos_iff.mpr (s.center ▸ (show s.x i.succ ≠ s.x 0 from ((show Injective s.x.ofLp from generic_conf _ s.avoids).ne (Fin.succ_ne_zero i))) : s.x i.succ ≠ 0)
    filter_upwards [he.eventually (gt_mem_nhds hr)] with k hk
    rw [cutoff.tsupport_eq]; simp only [Metric.mem_closedBall,not_le,dist_zero_right,PiLp.smul_apply,norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp k)),cutoff]
    exact (lt_inv_mul_iff₀ (hp k)).mpr (by simpa using hk)
  filter_upwards [eventually_all.mpr hu] with k hk
  have ht := window_stretch (x:= (e k)⁻¹ • s.x) (χ:=cutoff) (hp k) ⟨cutoff.contDiff, cutoff.hasCompactSupport, by
    simp only [PiLp.smul_apply,s.center,smul_zero]; exact cutoff.eventuallyEq_one, hk⟩
  rwa [smul_inv_smul₀ (hp k).ne'] at ht

lemma ae_skip (c : E4) (i : Axis) : ∀ᵐ z : E4, z i ≠ c i := by
  have ht := ((Measure.quasiMeasurePreserving_eval (fun _ : Axis => (volume : Measure ℝ)) i).comp (PiLp.volume_preserving_ofLp Axis).quasiMeasurePreserving).ae
      (show ∀ᵐ z : ℝ, z ≠ c i from by simp [ae_iff])
  exact ht

lemma ae_cons (x : Points n) (hx : x∈generic _) (hr : 0<r) : ∀ᵐ z : E4, Points.cons (r • z) x ∈ generic _ := by
  filter_upwards [ae_all_iff.mpr fun i : Fin n => ae_all_iff.mpr fun a => ae_skip (r⁻¹ • x i) a] with z hz a
  have hh i : (r • z) a ≠ x i a := by
    intro h; exact hz i a (by change z a = r⁻¹ * x i a; rw [← h]; exact (inv_mul_cancel_left₀ hr.ne' (z a)).symm)
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) j; exact fun h => (hh j h).elim
  refine Fin.cases (fun h => (hh i h.symm).elim) (fun j h => congr_arg Fin.succ ((hx a) h)) j

def draw (S : Table L) (v : Axis → Axis → L.Ref 4) : S.Stress := fun a b => S.project _ (v a b)

def parcel (J : S.Stress) (B : S.Field d) (V : E4 → E4) (i : ℕ) (s : Audience L) (r : ℝ) (a b : Axis) (z : E4) :=
  Work.A05.weight cutoff a (fun z => V z b) z *
    ((r:ℂ)^(3+i) * S.useAt S (Points.cons (r • z) s.x) (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ (S.classTokens ∘ s.tags))))

lemma parcel_eq (J : S.Stress) (B : S.Field d) (hv : Motion i V) (hr : 0<r) (s : Audience L) (a b : Axis) (z : E4) :
    parcel J B V i s r a b z = (r:ℂ)^4 * term J (stretch r cutoff) (fun y => V (y-s.x 0)) s.x (S.classTokens ∘ s.tags) B a b (r • z) := by
  simp only [parcel,term,D_stretch hr cutoff.contDiff,Work.A05.weight,s.center,sub_zero,hv.scales r hr,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_pow, pow_add,Complex.ofReal_mul,Complex.ofReal_inv]
  have hz : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

lemma parcel_integrable (J : S.Stress) (B : S.Field d) (hv : Motion i V) (hr : 0<r) (s : Audience L) (hw : Window s.x (stretch r cutoff)) (hs : S.Smooth) (a b : Axis) :
    Integrable (parcel J B V i s r a b) := by
  change Integrable (fun y => parcel J B V i s r a b y)
  simp_rw [parcel_eq J B hv hr]
  exact ((term_integrable J (stretch r cutoff) _ _ _ B hs (generic_conf _ s.avoids) hw a b ((hv.smooth b).continuous.comp (continuous_id.sub continuous_const))).comp_smul hr.ne').const_mul _

lemma scaled (J : S.Stress) (B : S.Field d) (hv : Motion i V) (hr : 0<r) (s : Audience L) :
    about J (stretch r cutoff) V s.x (S.classTokens ∘ s.tags) B = -∑ a, ∑ b, ∫ z, parcel J B V i s r a b z := by
  have ht (a b : Axis) := Measure.integral_comp_smul_of_nonneg volume (term J (stretch r cutoff) (fun y => V (y-s.x 0)) s.x (S.classTokens ∘ s.tags) B a b) r (hR := hr.le)
  have hz : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp_rw [parcel_eq J B hv hr,integral_const_mul,ht,show Module.finrank ℝ E4 = 4 from finrank_euclideanSpace_fin,
    Complex.real_smul, Complex.ofReal_inv,Complex.ofReal_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hz)]
  rfl

def mass (V : E4 → E4) (a b : Axis) (z : E4) := ‖Work.A05.weight cutoff a (fun z => V z b) z‖

lemma annular_test (hs : S.Symmetric) (v : Axis → Axis → L.Ref 4) (B : L.Ref d) (s : Fin m → Audience L) (c : Fin m → ℂ)
    (a b : Axis) (hr : 0<r) (hv : Motion i V)
    (he : ∀ z : E4, 1/4 ≤ ‖z‖ → ‖z‖ ≤ 1 → (∀ j, Points.cons (r • z) (s j).x ∈ generic _) →
        ‖∑ j, c j * ((r:ℂ)^(3+i) * pairRead S (v a b) B (s j) (r • z))‖ ≤ ε) :
    ‖∫ z, ∑ j, c j * parcel (draw S v) (S.project d B) V i (s j) r a b z‖ ≤ (∫ z, mass V a b z) * ε := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_weight cutoff.contDiff cutoff.hasCompactSupport a (hv.smooth b).continuous).norm.mul_const ε) ?_
  filter_upwards [ae_all_iff.mpr fun j => ae_cons (s j).x (s j).avoids hr] with z hz
  let w := Work.A05.weight cutoff a (fun z => V z b) z
  change _ ≤ ‖w‖ * ε
  by_cases hw : w=0
  · simp [parcel,hw,show Work.A05.weight cutoff a (fun z => V z b) z=0 from hw]
  have hp := weight_off _ _ hw
  have ht j : parcel (draw S v) (S.project d B) V i (s j) r a b z = w * ((r:ℂ)^(3+i) * pairRead S (v a b) B (s j) (r • z)) := by
    have hh := S.at_project S hs (fun _ => le_rfl) (generic_conf _ (hz j)) (Fin.cons ⟨4,v a b⟩ (Fin.cons (α:=fun _ => L.Token) ⟨d,B⟩ (s j).tags))
    rw [Fin.comp_cons, Fin.comp_cons] at hh
    unfold parcel pairRead draw; rw [← hh]
  simp_rw [ht,mul_left_comm (c _) w, ← Finset.mul_sum,norm_mul]
  exact mul_le_mul_of_nonneg_left (he z hp.1 hp.2 hz) (norm_nonneg _)

lemma shrunk (hs : S.Hierarchy) (hd : W.Derivatives S) {v : Axis → Axis → L.Ref 4} (hJ : Conserved W H (draw S v)) (B : L.Ref d)
    (hv : Motion i V) (hS : Snip S v B D (3+i)) (s : Fin m → Audience L) (c : Fin m → ℂ) (χ : Fin m → E4 → ℝ)
    (hw : ∀ j, Window (s j).x (χ j)) (hc : ∀ u, ∑ j, c j * S.injectFront (s j).tags (s j).x D u = 0) :
    ∑ j, c j * about (draw S v) (χ j) V (s j).x (S.classTokens ∘ (s j).tags) (S.project d B) = 0 := by
  let J := draw S v; let p := S.project d B
  let P (r) j a b := parcel J p V i (s j) r a b
  obtain ⟨e,ε,h0,hE,he,hk⟩ := hS m s c hc
  have hW := eventually_all.mpr fun j => eventual_stretch (s j) (fun k => (h0 k).1) hE
  let A (k : ℕ) (a b : Axis) := ∫ z, ∑ j, c j * P (e k) j a b z
  have hT (a b : Axis) : Tendsto (fun k => A k a b) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (mul_zero (∫ z, mass V a b z) ▸ he.const_mul _)
    filter_upwards [hk] with k hk
    exact annular_test hs.laws.toSymmetric v B s c a b (h0 k).1 hv (fun z hz hH h => hk z hz hH h a b)
  let F := ∑ j, c j * about J (χ j) V (s j).x (S.classTokens ∘ (s j).tags) p
  have ht : ∀ᶠ k : ℕ in atTop, F = -∑ a, ∑ b, A k a b := by
    filter_upwards [hW] with k hk
    have hq j := independent_about hs.smooth hd hJ V hv.smooth hv.rigid (generic_conf _ (s j).avoids) (hw j) (hk j) (S.classTokens ∘ (s j).tags) p
    have hh a b j := (parcel_integrable J p hv (h0 k).1 (s j) (hk j) hs.smooth a b).const_mul (c j)
    have he j : about J (χ j) V (s j).x (S.classTokens ∘ (s j).tags) p = -∑ a, ∑ b, ∫ z, P (e k) j a b z := hq j |>.trans (scaled J p hv (h0 k).1 _)
    have ha a b : A k a b = ∑ j, c j * ∫ z, P (e k) j a b z := by
      dsimp only [A]; rw [integral_finsetSum _ fun j _ => hh a b j]; simp_rw [integral_const_mul]; rfl
    simp_rw [F,he,mul_neg,Finset.sum_neg_distrib,Finset.mul_sum,ha]
    rw [Finset.sum_comm]; congr 1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hl := ((tendsto_finsetSum Finset.univ fun a _ => tendsto_finsetSum _ fun b _ => hT a b).neg).congr' (show _ =ᶠ[atTop] (fun _ : ℕ => F) from ht.mono fun _ h => h.symm)
  change F = 0; simpa using tendsto_nhds_unique (tendsto_const_nhds (x:=F)) hl
end YM.StressFlux.Annular
