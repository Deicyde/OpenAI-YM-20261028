import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Stock
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.TensorCost
import YM.SectorNext.LARGE_FIELD_REMAINDERS.CenteredCharge
import YM.Work.A05



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Sharper one-step support & output-factor reprice at represented inputs

 demands keeping *full* clipped output base, even when doing engineering
charges on defects. Here show sector-analytic estimates can deliver at that
factor AND with absolute list sums on the still unassembled gas integrals,
with explicit C_L^links bulk loss compared to precise volume Gaussian scaling.
No assumption about covariance, not asserting this loss is affordable at
normalization: just purchasing the β powers and seed price. May work on this
with e.g. localized determinant or reference comparisons later. No v normalization
claim. Distinguish this from pmult/local exponent comparisons in Affine:
we handle whole true coarse *base* tail, not pulling off arbitrary densities by
proclaiming an estimator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Reprice
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric Oriented Presented Exterior Bloch Work.F03 LabelSum
  Next.Fluctuations.Sector Center
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)

def kinetic (m : BudgetPoint) (V : Config G c) := averaged fun s : Signed => ∑ i : Cell c, T.down.baseTerm T.low m (pull s 0 V) i

def normedBulk (S : StepData c f) (F : Forest S.ratio) (G : Gauge) (x β D : ℝ) :=
  Real.exp (3*(nf f:ℝ))* shore S G F .shielded β x D

private lemma gauge_cap (P : Teller G) (L : Side) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L=L → P.Funds S T →
    ∀ (m : BudgetPoint), temp x = m.threshold → ∀ V β, 0≤β → β ≤ 2*y G L x →
    β*(kinetic T m V-meanCut T x V) ≤ nf c := by
  let n : ℝ := Fintype.card PlaqAxes
  let C := P.below.paths
  let σ := P.below.width / L.val
  have hs : 0<σ := div_pos P.below.width_pos (by positivity)
  have ht := (Scales.cutoff G L 0 0 hs).const_mul (n*8*C^2); simp only [pow_zero,one_mul,mul_zero] at ht
  filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one),(year G L).eventually_gt_atTop 0] with x hx hy
  intro c f S T hL hT p hp V β he hβ
  obtain ⟨d,b,hU,hV⟩ := hT.feeds
  rw [← hT.low] at hV
  let k := 4*C^2*Real.exp (-σ*till x)
  have hh (s : Signed) (i : Cell c) : cuff T.down T.low p S.patch.L.val (till x) (pull s 0 V) i ≤ k := by
    have h := cuff_pay hV p i (pull s 0 V) _ (till x) S.patch.L.property
    apply (le_abs_self _).trans (h.trans_eq ?_)
    unfold k σ C; rw [hL]; ring_nf; rfl
  let E : ℝ := nf c
  have hE : 0≤E := Nat.cast_nonneg _
  have hh' s := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh s i)
  unfold kinetic meanCut cutOutput; rw [← av_sub]
  unfold cuff at hh'; simp only [← hp,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Cell,Face,Fintype.card_prod,Nat.cast_mul] at hh'; change ∀ s, _ ≤ E*n*k at hh'
  apply (mul_le_mul_of_nonneg_left ((av_mono hh').trans_eq (av_const _)) he).trans -- implicit
  have hk : 0 ≤ k := by unfold k; positivity
  have he := mul_le_mul_of_nonneg_right hβ (mul_nonneg (mul_nonneg hE (Nat.cast_nonneg (Fintype.card PlaqAxes))) hk)
  apply he.trans; unfold k; change _ ≤ E
  have hh := mul_le_mul_of_nonneg_right (show n*8*C^2*(y G L x * Real.exp (-σ*till x)) ≤ 1 from hx) hE; nlinarith only [hh]

private lemma each_int (R : Rep G f) {σ C Λ δ w : ℝ} (hr : R.Lawful σ C Λ δ w) (F : Forest S.ratio)
    (x : ℝ) (B : Finset ℕ) : Integrable (fun a => separate R (till x) B (F.drape a)) (F.order G) := by
  let F0 U := Real.exp (R.beta * cutR R (till x) U)
  let g := R.activities.gasOccurrence R.p B
  apply ((Env.along (A:=Config G f) (F:=fun U => F0 U*Real.exp (R.exponent U)*g U) ?_ F.continuous_drape.measurable)).integrable
  have hg : Envelope g := by
    have hx := (Activities.gasSeries hr.labels)
    obtain ⟨C,-,H⟩ := hx
    exact ⟨Measurable.ite (R.activities.admissible_borel R.p B) (Finset.measurable_fun_prod _ fun i _ => hr.labels.forced.meas i) measurable_const,C B,H B⟩
  have hr' : Envelope F0 := ((Envelope.const _).mul (env_mean (F:=fun s U => ∑ i, crown R.path R.clip (till x) 1 R.p.threshold (pull s 0 U) i) fun i =>
    Envelope.sum _ _ fun _ => Env.along (env_crown hr.paths ..) (continuous_pull i 0).measurable)).exp
  exact (hr'.mul (R.exponentEnv hr).exp).mul hg

def si (x β : ℝ) (A : Stores S) (V : Config G c) (k : S.Choices) (F : Forest S.ratio) (a : F.Slice G) :=
  sieve T β x V * leaves A T β x k V (F.drape a)

def Kterms {x W : ℝ} (d : Allocation G S x W) (F : Forest S.ratio) (A : Stores S) (V : Config G c) (R : Rep G f)
    (i : Finset ℕ) (k) a := d.bill A k (F.drape a) V * (si T x R.beta A V k F a * separate R (till x) i (F.drape a))

def earnable {x W : ℝ} (d : Allocation G S x W) (F : Forest S.ratio) (A : Stores S) (V : Config G c) (R : Rep G f)
    (m : BudgetPoint) (u κ : ℝ) (i : Finset ℕ) :=
  Real.exp u * earn S G x κ R.beta A.shares * Real.exp (R.beta*kinetic T m V) *
    tagTotal F (fun k a => ‖Kterms T d F A V R i k a‖)

set_option maxHeartbeats 900000 in
/-- Preserve full oriented *base* at the output, all actual tags and addresses,
per A (need summability if not accepting an additional per-unit loss; not asserting
comparison to infinite volume free determinant normalized bill). Provide even
bill on the sum over label sets of **integrals of norms**, not just integrable
after taking the `tsum` of functions. Applied before any changing order. H &
n may also include downstream geometry costs; not claiming those suffice.
-/
theorem compare (P : Teller G) (L : Side) (W : ℝ) (hw : 0<W) : ∃ D : ℝ, 1 ≤ D ∧ ∀ (κ H σ C : ℝ) (n : ℕ),
    0 < κ → 0 ≤ H → 0 < σ → 0 < C → ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
    S.patch.L=L → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
    ∀ (d : Allocation G S x W) (F : Forest S.ratio) (A : Stores S) (V : Config G c) (R : Rep G f)
    (Λ δ w : ℝ) (m : BudgetPoint),
    R.Lawful σ C Λ δ w → (Λ ≤ 2*p G L x) → (w∈Set.Icc (0:ℝ) 1) → (δ ≤ 1) →
      R.p.threshold = fiery G x L → m.threshold = temp x → R.beta ∈ Set.Icc (y G L x/2) (2*y G L x) →
      let u := coin G L H n x*A.shares
      let O := Real.exp R.scalar * normedBulk S F G x R.beta D * Real.exp (-seed G L x κ R.beta A.shares/4)
      (∀ i k, Integrable (Kterms T d F A V R i k) (F.order G)) ∧
        SumBudget (earnable T d F A V R m u κ) O ∧
          Real.exp u * earn S G x κ R.beta A.shares * Real.exp (R.beta*kinetic T m V) * leftOver d F T R A V ≤ O := by
  obtain ⟨D,hD,h⟩ := no_sieve (E:=ℝ) P L W hw
  refine ⟨D,hD,fun κ H σ C n hk hH hs hc => ?_⟩
  have hp := Scales.inactive_price G L n (a:=2) two_pos
  have h0 := hp.const_mul (H+4); simp only [Real.rpow_two,mul_zero] at h0
  filter_upwards [h κ 0 n hk le_rfl,bulk_price G L σ C (error:=fun _ => (0:ℝ)) (by simp only [mul_zero]; exact tendsto_const_nhds) hs hc,
    gauge_cap P L,h0.eventually (ge_mem_nhds (show 0<κ/8 by positivity)),(year G L).eventually_gt_atTop 1] with x ht hx hW hQ hy
  intro c f S T hL hV hT d F A V R Λ δ w m hE ha hw he hF hm hβ u O
  let z := y G L x
  let β := R.beta
  have hb : 0≤β := le_trans (by linarith only [hy] : 0 ≤ y G L x / 2) hβ.1
  have hv : β*kinetic T m V + (-β*meanCut T x V) ≤ nf c := by linarith [hW S T hL hT _ hm.symm V β hb hβ.2]
  have hcap : air R x σ C Λ δ ≤ 2 := by simpa only [mul_zero,add_zero] using hx f R δ Λ he ha hF hβ (le_refl _)
  obtain ⟨b,hm,hx⟩ := occurrence_budget A R.activities R.p d hw.1 hE.labels (hL.symm ▸ hF)
  let N (j : F.Slice G) := F.drape j
  let Y := Real.exp (R.scalar+air R x σ C Λ δ*(nf f:ℝ))
  have hS (i : F.Slice G) k (hl : d.bill A k (N i) V ≠0) := exposed_absolute A d R hw.1 hm hx hE hb (N i) V k hl
  let E := earn S G x κ β A.shares; let l := Real.exp (β*kinetic T m V)
  let s := shore S G F Mode.shielded β x D
  have HN : 0≤s := by
    have hi := prefactor_pos (S:=S) (G:=G) β
    have hk : 0<g G S.patch.L x := Scales.gauge _ _ (by rw [hL]; exact zero_lt_one.trans hy)
    unfold s shore Mode.size; positivity
  have Hs : 0≤E := (earn_pos ..).le
  let h := seed G L x κ β A.shares
  have total (g : S.Choices → F.Slice G → ℝ) (q : ℝ) (hs : 0 ≤ q) (hg : ∀ i, Integrable (g i) (F.order G))
      (he : ∀ k i, d.bill A k (N i) V ≠0 → ‖g k i‖ ≤ Y*q) :
      let b k i := d.bill A k (N i) V * (si T x β A V k F i * g k i)
      (∀ k, Integrable (b k) (F.order G)) ∧
      Real.exp u * E*l*tagTotal F (fun k i => ‖b k i‖) ≤ Real.exp u * (Real.exp (R.scalar+3*(nf f:ℝ))*q)*s*Real.exp (-h/2) := by
    intro b
    have hBB := funds_branch hT; have hi := F.continuous_drape (G:=G) |>.measurable
    have hz := fun k => (d.envelope hBB hi (V:=fun _ => V) measurable_const A k)
    have hh k := (env_leaves hT A β x k hi (V:=fun _ => V) measurable_const)
    refine ⟨fun k => d.portion_integrable hBB A F V (fun k a => si T x β A V k F a • g k a) k
      (Env.smul_L1 ((Envelope.const (sieve T β x V)).mul (hh k)) (hg k)),?_⟩
    let B := Real.exp (-β*meanCut T x V)
    have hZ := ht S T hL hV hT d F V A true β (Y*q) g (mul_nonneg (Real.exp_pos _).le hs) hβ hg
      (fun k => Eventually.of_forall fun a hh _ => by simp only [coin,zero_mul,Real.exp_zero,mul_one]; exact he _ _ hh)
    simp only [smul_eq_mul,clip_mean] at hZ
    let weight k a := d.bill A k (N a) V * (leaves A T β x k V (N a) * g k a)
    have hG k a : ‖b k a‖ = B * ‖weight k a‖ := by unfold b weight si; rw [show _*( _ * _ * g k a) = B * (d.bill A k (N a) V*(leaves A T β x k V (N a)*g k a)) by unfold N B meanCut cutOutput sieve; ring,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    change E * tagTotal F (fun k a => ‖weight k a‖) ≤ Y*q*s*Real.exp (-h/2) at hZ
    unfold tagTotal; simp_rw [hG,integral_const_mul,← Finset.mul_sum]; change _ * E * l * (B * tagTotal F _) ≤ _
    have h2 : l*B*Y ≤ Real.exp (R.scalar +3*(nf f:ℝ)) := by
      unfold l B Y; rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_monotone (by
        have hz := mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg (α:=ℝ) (nf f)); have hx := Nat.cast_le (α:=ℝ).mpr (nf_le S); linarith only [hv,hz,hx])
    have hp : 0≤Real.exp u*l*B := by unfold l B; positivity
    have hh := mul_le_mul_of_nonneg_left hZ hp
    have hz := mul_le_mul_of_nonneg_left h2 (show 0≤Real.exp u*q*s*Real.exp (-h/2) by positivity)
    linarith only [hh,hz]
  have hK i := total (fun k a => separate R (till x) i (N a)) (b i) (hm.1 _) (fun k => each_int R hE F x i)
    (fun k a hh => (hS a k hh).1 i)
  let d0 := Real.exp u * Real.exp (R.scalar+3*(nf f:ℝ))*s*Real.exp (-h/2)
  have hD' : 0 ≤ d0 := by unfold d0; positivity
  have hM i : earnable T d F A V R m u κ i ≤ d0*b i := by
    apply ((hK i).2).trans_eq; unfold d0; ring
  have ha' : u+w*4*A.shares ≤ h/4 := by
    let q := p G L x
    have hp : 0<q := Scales.pos G L x
    have hh1 : (H+4)*(Scales.b x^n*(1+Real.log z)/q^2) ≤ κ/8 := hQ
    rw [← mul_div_assoc,div_le_iff₀ (sq_pos_of_pos hp)] at hh1
    have hx := earned G L (m:=A.shares) (zero_lt_one.trans hy) hk.le hβ.1
    have he : 1 ≤ Scales.b x^n*(1+Real.log z) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (Scales.size _))
      (le_add_of_nonneg_right (Real.log_nonneg hy.le))
    unfold u coin; change H*_*_*_+w*4*_ ≤ _; change κ/2*q^2*(A.shares:ℝ) ≤ h at hx
    have hi' := mul_le_mul_of_nonneg_right hh1 (Nat.cast_nonneg (α:=ℝ) A.shares)
    have hp := mul_le_mul_of_nonneg_right (show w ≤ Scales.b x^n*(1+Real.log z) from hw.2.trans he) (Nat.cast_nonneg (α:=ℝ) A.shares)
    unfold z at *; nlinarith only [hi',hp,hx,hw.2]
  have hl : d0 * Real.exp (w*4*A.shares) ≤ O := by
    have hm : u+(-h/2)+w*4*A.shares ≤ -h/4 := by linarith
    unfold d0 O normedBulk; rw [Real.exp_add R.scalar]
    have he := mul_le_mul_of_nonneg_left (Real.exp_monotone hm) (show 0≤Real.exp R.scalar * Real.exp (3*(nf f:ℝ))*s by positivity)
    rw [Real.exp_add (u+_), Real.exp_add u] at he -- order
    unfold h s at he; unfold h s; linarith only [he]
  have ht i : 0 ≤ earnable T d F A V R m u κ i := by
    unfold earnable; refine mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le Hs) (Real.exp_pos _).le) ?_
    exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))
  have h1 := hm.2.1.mul_left d0
  have h2 := h1.of_nonneg_of_le ht hM
  refine ⟨fun i => (hK i).1,⟨ht,h2,(h2.tsum_le_tsum hM h1).trans (by rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left hm.2.2 hD').trans hl)⟩,?_⟩
  let g a := ‖exposed R (till x) (N a)‖
  have hg : Integrable g (F.order G) := ((Env.along (env_exposed R hE (till x)) F.continuous_drape.measurable).integrable _).norm
  have hq := (total (fun _ a => g a) _ (Real.exp_pos _).le (fun _ => hg) (fun k a ha => by rw [Real.norm_of_nonneg (show 0 ≤ g a from norm_nonneg _)]; exact (hS a k ha).2)).2
  change Real.exp u*E*l*leftOver d F T R A V ≤ _
  let Z k a := leaves A T β x k V (N a)
  change Real.exp u*E*l*tagTotal F (fun k a => ‖d.bill A k (N a) V*(si T x β A V k F a * g a)‖) ≤ _ at hq
  rw [show leftOver d F T R A V=tagTotal F (fun k a => ‖d.bill A k (N a) V*(si T x β A V k F a * g a)‖) by
    unfold leftOver tagTotal Allocation.column tagTotal Allocation.portion; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with a
    have hh : 0 ≤ Z k a := mul_nonneg (S.likelihood_pos ..) (Real.exp_pos _).le
    have ha := d.nonneg A k (N a) V
    simp only [smul_eq_mul]; unfold si
    rw [Real.norm_of_nonneg (show 0≤d.bill A k (N a) V*(sieve T β x V* _ * g a) from mul_nonneg ha (mul_nonneg (mul_nonneg (Real.exp_pos _).le hh) (norm_nonneg _)))]
    unfold β g N; ring]
  apply hq.trans (le_trans ?_ hl); unfold d0; ring_nf; rfl
end YM.SectorNext.Remainder.Reprice
