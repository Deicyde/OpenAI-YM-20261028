import YM.Further.CURVED_GAUSSIAN_JETS.Doses

/-!
# Ordered E_u and AC-I power corrections under integrated left jets

All comparisons for the ACTUAL Panel line, windows & shared Gram table at
that U. Exercises the two extractions/sums, with the price in true ordered
left derivatives of these (matrix-product) numerical terms. Does not give
connected-support hit charges over all possible addresses. Decay in BOTH N
and number of ordered factors; to pay any finite per-factor exponents one
can decrease `q` before choosing N. Never differentiate a V-dependent switch
of the matrix or its windows here, nor require dominance at an open set of
all possible *sector outputs*. Need a valid extension per tested object.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson RG Precision Progress.StationaryScenes
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
open Next.Foundations (left_has leftDerivs_chart)
variable {n c : Side} {G : Gauge} {I : Type*} [Fintype I] [DecidableEq I] (W : Windows I) {a : I → Site n}
    {U : Config G c} {A : Field G c I} {s : Weights a} {M : ℝ} {l : Word G c} {k N : ℕ}
    {Q : Directions G c → Prop} {p : Prices}

lemma Cash.pow (h : Good A k U) {r C : ℝ} (ha : Cash s r k Q U A C) (hp : 0≤C) (hr : 0≤s.width r k) (j : ℕ) :
    Cash s r k Q U (fun V=> (A V)^j) ((s.pay k*C)^j) := by
  induction j with
  | zero => simp only [pow_zero]; exact cash_one
  | succ j ih => simpa only [pow_succ',←mul_assoc] using! ha.product ih h (h.pow j) hr hp (pow_nonneg (mul_nonneg (s.pay_pos k).le hp) _)

def qd (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) (N : ℕ) := s.pay k*defect_cost p s k M * Real.exp (-spare p*N)
def qr (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) (N : ℕ) := s.pay k*line_cost p s k M * Real.exp (-spare p*N)
lemma q_widths (hm : 0≤M) : 0 ≤ qd p s k M N ∧ 0 ≤ qr p s k M N := by
  obtain ⟨h1,h2,h3,h4⟩ := cost_pos p s k hm; have := s.pay_pos k; unfold qd qr; constructor <;> positivity
lemma q_delay (q : ℝ) (hq : 0<q) : ∀ᶠ N : ℕ in atTop, p.deep N<1 ∧ p.error N<1 ∧ qd p s k M N<q ∧ qr p s k M N<q := by
  have ht (x : ℝ) : ∀ᶠ N : ℕ in atTop, x*Real.exp (-spare p*N)<q := by
    apply Tendsto.eventually_lt_const hq
    simpa only [Function.comp_def,neg_mul,mul_zero] using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (spare_pos p))).const_mul x)
  exact (p.vanishes.eventually_lt_const zero_lt_one).and ((p.delay.eventually_lt_const zero_lt_one).and ((ht _).and (ht _)))

def path (W : Windows I) (A : Field G c I) (d : ℕ) (u : ℝ) : Field G c I := fun V=> W.chain (A V) (d+1) u
def provided (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) (N : ℕ) (q : ℝ) (i : I) (j d : ℕ) :=
    (s.pay k * column_cost p s k M * qd p s k M N * q^d)*s.τ i^j
variable {q : ℝ} (hb : W.Includes a N) (hd : qd p s k M N≤q) (hr : qr p s k M N≤q)
    (h : Street p s k Q A U M)
include h
lemma Street.path (u : ℝ) (hu : 0≤u) (d : ℕ) : Good (Jets.path W A d u) k U :=
    (h.probe W hu).prod ((h.err W hu).neg.pow _)
lemma Street.path_flow (d : ℕ) : Flow (Jets.path W A d) U k :=
    (h.column_flow W).prod ((h.defect_flow W).neg.pow (fun _ hu=>(h.err W hu.le).neg) _) (fun _ hu=>⟨h.probe W hu.le, (h.err W hu.le).neg.pow _⟩)
include hb hd
lemma Street.path_cost (i j : I) (d : ℕ) (hl : l.length≤k) (hv : ∀ i∈l,Q i) {u : ℝ} (hu : 0≤u) :
    ‖leftDerivs (fun V=> Jets.path W A d u V i j) l U‖ ≤ provided p s k M N q i l.length d*Line.bell u := by
  have he := h.space (r:=2*spare p) (by linarith only [spare_pos p])
  obtain ⟨hv1,hv2,hv3,hv4⟩ := cost_pos p s k h.has
  have hq := (q_widths (p:=p) (s:=s) (k:=k) (N:=N) h.has).1
  have hi := s.pay_pos k
  have hg := ((columns_pay W h hu).mono (show 2*spare p≤3*spare p by linarith only [spare_pos p]) le_rfl).product
    ((defect_pay W h hb hu).neg.pow (h.err W hu).neg (by positivity) he (d+1))
    (h.probe W hu) ((h.err W hu).neg.pow (d+1)) he (by positivity) (by positivity) l hl hv
  apply ((hg.1.entry (he.trans (s.width_le _ _ _ hl)) i j) : ‖leftDerivs _ _ _‖ ≤ _).trans
  have hm : 0 ≤ s.τ i ^ l.length := pow_nonneg (s.nonneg i) _
  rw [←mul_div_assoc (s.pay k),←mul_div_assoc (s.pay k),←mul_assoc (s.pay k) (defect_cost ..),← qd, pow_succ']
  calc
    _ ≤ s.pay k* column_cost p s k M / (1+u) * ((qd p s k M N/(1+u)) * q^d) * s.τ i^l.length := by
          gcongr; exact (div_le_self hq (by linarith)).trans hd
    _ = _ := by unfold Line.bell provided; rw [pow_two,one_div,mul_inv]; ring
lemma Street.path_terms (i j : I) (d : ℕ) : Terms (volume.restrict (Ioi 0)) (Ioi 0) Q (fun u V=> Jets.path W A d u V i j) k
    (fun j u => provided p s k M N q i j d*Line.bell u) U :=
  ⟨fun l hl _=>(h.path_flow W d l hl i j).aestronglyMeasurable measurableSet_Ioi,fun _ hl hv _ hu=>h.path_cost W hb hd i j d hl hv (le_of_lt hu),
    fun _ hl _ v _ u hu => (h.path W u (le_of_lt hu) d).has hl v i j⟩

omit h
variable (hh : ∀ᶠ V in 𝓝 U, Street p s k Q A V M)
include hh
lemma tail_terms (i j : I) : Terms Measure.count univ Q (fun d V=> W.tail (A V) d i j) k
    (provided p s k M N q i) U := by
  have he := ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))
  have hm d z (_:z≤k) := Line.bell_int.1.const_mul (provided p s k M N q i z d)
  have ht d := hh.mono fun V hv => hv.path_terms W hb hd i j d
  refine ⟨fun _ _ _=> Measurable.of_discrete.aestronglyMeasurable,fun l hl hv d _=> ?_,fun l hl hv v hq d _=>live_total he (hm d) (ht d) hl hv hq⟩
  apply (paid_total he (hm d) (ht d) hl hv).trans_eq; rw [integral_const_mul,Line.bell_int.2,mul_one]
omit hh hb hd in
lemma provided_sum (hq : 0≤q) (hq' : q<1) (i : I) (d : ℕ) :
    HasSum (provided p s k M N q i d) (s.pay k * column_cost p s k M * qd p s k M N * (1-q)⁻¹ * s.τ i^d) :=
    (((hasSum_geometric_of_lt_one hq hq').mul_left _).mul_right _)
lemma tail_price (hq : q<1) (i j : I) (hl : l.length≤k) (hv : ∀ i∈l,Q i) :
    let f := fun d V=> W.tail (A V) d i j
    leftDerivs (fun V => ∑' d, f d V) l U = ∑' d, leftDerivs (f d) l U ∧
      Summable (fun d => leftDerivs (f d) l U) ∧
      ∑' d, ‖leftDerivs (f d) l U‖ ≤ s.pay k * column_cost p s k M * qd p s k M N * (1-q)⁻¹ * s.τ i^l.length := by
  intro f
  have hx := (q_widths hh.self_of_nhds.has).1.trans hd; have H := inside_infinite (fun d (_:d≤k)=>(provided_sum hx hq i d).summable)
    (hh.eventually_nhds.mono fun V hV=>tail_terms W hb hd hV i j) hl hv
  exact ⟨H.1,H.2.1,H.2.2.trans_eq (provided_sum hx hq i _).tsum_eq⟩

/-- Numerical jet estimate summable in number of intervening blocks,
with slack spatial weights. Valid for q arbitrarily small after increasing
the delay (`q_delay`); use that when needing to include a per-chain
expansion cost or endpoint factors. No algebra at a cut branch derivative.
-/
theorem window_log_error (hq : q<1) (hN : p.deep N<1) (hl : l.length≤k) (hv : ∀ i∈l,Q i) (i : I) :
    let g := fun V => W.tollLine (A V) p.mass i - price A p i V
    let f := fun d V => W.tail (A V) d i i
    leftDerivs g l U = leftDerivs (price (slab W A i) p (W.center i)) l U - leftDerivs (price A p i) l U ∧
      leftDerivs g l U = ∑' d, leftDerivs (f d) l U ∧
      |leftDerivs g l U| ≤ s.pay k * column_cost p s k M * qd p s k M N * (1-q)⁻¹ * s.τ i ^ l.length := by
  intro g f
  have he := hh.mono fun V hV=> show g V=(fun V => ∑' d,f d V) V by linarith only [show price A p i V = W.tollLine (A V) p.mass i - ∑' d,f d V from W.line_tables hV.base hb hN i]
  have ht := tail_price W hb hd hh hq i i hl hv
  constructor
  · clear he ht; induction l generalizing U with
    | nil => rfl
    | cons d l ih =>
      obtain ⟨hd,hv'⟩ := List.forall_mem_cons.mp hv
      exact ((((paid_dose (hh.mono fun V hV=>hV.slab W i) hl hv _).2.2 d l rfl).sub ((paid_dose hh hl hv _).2.2 d l rfl)).congr_of_eventuallyEq
        (((Multi.Puff.swing U d).eventually hh.eventually_nhds).mono fun t h=>ih h (Nat.le_of_succ_le hl) hv')).deriv
  rw [left_on he l,ht.1]; exact ⟨rfl,(norm_tsum_le_tsum_norm ht.2.1.norm).trans ht.2.2⟩

omit hh hd
include h hr
lemma Street.power_cost (ht : ∀ᶠ V in 𝓝 U,(A V).IsHermitian) (d : ℕ) : Cash s (2*spare p) k Q U
    (fun V=> (-(Jets.coeff W A V))^(d+1)) (qr p s k M N*q^d) := by
  have hy := (cost_pos p s k h.has).2.2.2
  have hx := (q_widths h.has).2.trans hr
  have he := (coeff_pay W h hb ht).neg.pow ((h.coeff W).neg) (by positivity) (h.space (by linarith only [spare_pos p])) (d+1)
  rw [←mul_assoc,←qr,pow_succ'] at he
  exact he.mono le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q_widths h.has).2 hr _) (q_widths h.has).2)

def bead (W : Windows I) (A : Field G c I) (d : ℕ) (V : Config G c) := (-(d+1:ℝ)⁻¹) • ((-(Jets.coeff W A V))^(d+1))
lemma Street.bead_terms (i j : I) (ht : ∀ᶠ V in 𝓝 U,(A V).IsHermitian) : Terms Measure.count univ Q
    (fun d V=> Round.ripple (Jets.coeff W A V) d i j) k (fun m d => (qr p s k M N*q^d)*s.τ i^m) U := by
  have he (d : ℕ) : (fun V=> Round.ripple (Jets.coeff W A V) d i j) = (fun V=> bead W A d V i j) := funext fun V=>by simp only [bead, Matrix.smul_apply,smul_eq_mul,Round.ripple]; ring
  rw [show (fun (d : ℕ) V => Round.ripple (Jets.coeff W A V) d i j) = _ from funext he]
  refine ⟨fun _ _ _=>Measurable.of_discrete.aestronglyMeasurable,fun l hl hv d _ => ?_, fun l hl hv e hd d _=> (((h.coeff W).neg.pow (d+1)).scale (-(d+1:ℝ)⁻¹)).has hl e i j⟩
  change ‖jet l (bead W A d) U i j‖ ≤ _
  have H := ((h.power_cost W hb hr ht d) l hl hv).scale (-(d+1:ℝ)⁻¹)
  unfold bead; rw [jet_scale]
  refine (H.1.entry ((h.space (by linarith only [spare_pos p])).trans (s.width_le _ _ _ hl)) i j).trans ?_
  have hx := s.nonneg i; have hy := (q_widths h.has).2.trans hr; have ht := (q_widths (p:=p) (s:=s) (k:=k) (N:=N) h.has).2
  rw [abs_neg,abs_of_pos (by positivity),mul_assoc]; exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ (by simp))
omit h
include hh
lemma correction_error (hq : q<1) (hl : l.length ≤ k) (hv : ∀ i∈l,Q i) (i : I) :
    let f := fun d V => Round.ripple (coeff W A V) d i i
    leftDerivs (fun V => Round.onLine (coeff W A V) i) l U = ∑' d,leftDerivs (f d) l U ∧
      Summable (fun d => leftDerivs (f d) l U) ∧
        ∑' d, ‖leftDerivs (f d) l U‖ ≤ qr p s k M N*(1-q)⁻¹*s.τ i^l.length := by
  intro f
  have hm := hh.mono fun _ h=>h.base.symm
  have hs j := (((hasSum_geometric_of_lt_one ((q_widths hh.self_of_nhds.has).2.trans hr) hq).mul_left (qr p s k M N)).mul_right (s.τ i^j))
  have he := inside_infinite (fun j (_:j≤k)=> (hs j).summable) ((hh.and hm.eventually_nhds).mono fun V hv=> hv.1.bead_terms W hb hr i i hv.2) hl hv
  exact ⟨he.1,he.2.1,he.2.2.trans_eq (hs _).tsum_eq⟩

lemma true_det (ht : p.error N<1) :
    ∀ᶠ V in 𝓝 U, let C := covariance W A V
    C.PosDef ∧ Real.log C.det = ∑ i, (-price A p i V + Round.onLine (coeff W A V) i) := by
  filter_upwards [hh] with V hv
  have he := W.correction_bill hv.base hb
  have hE := Rows.unweighted he p.speed_pos.le
  intro C; refine ⟨(W.correction_ratio hv.base hb ht).1, ?_⟩
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    obtain ⟨i⟩ := h
    have h := Panel.bill_quad hv.base.symm hv.base.numeric i
    unfold C covariance
    rw [Finset.sum_add_distrib,Finset.sum_neg_distrib,covariance_log hv.base.pos (W.blend_symm _) hE (p.error_pos N).le ht,
      Round.lines _ hE (p.error_pos N).le ht,Panel.log_form (A V) hv.base.symm hv.base.numeric p.gap_pos (h.1.trans h.2)]; rfl



theorem precision_terms (hq : q<1) (ht : p.error N<1) (hl : l.length ≤ k) (hv : ∀ i∈l,Q i) (i j : I) :
    let f := fun (d : ℕ) V => (((-(coeff W A V))^(d+1))* A V) i j
    leftDerivs (fun V => ((covariance W A V)⁻¹ - A V) i j) l U = ∑' d,leftDerivs (f d) l U ∧
      Summable (fun d => leftDerivs (f d) l U) ∧
        ∑' d, ‖leftDerivs (f d) l U‖ ≤ (s.pay k*(qr p s k M N*(1-q)⁻¹)*M) * s.τ i^l.length := by
  intro f
  unfold covariance; rw [left_on (g:=fun V=>∑' d,f d V) (hh.mono fun V hV=> ((W.correction_ratio hV.base hb ht).2.2 i j).tsum_eq.symm) l]
  have hs (z : ℕ) := (((((hasSum_geometric_of_lt_one ((q_widths hh.self_of_nhds.has).2.trans hr) hq).mul_left (qr p s k M N)).mul_left (s.pay k)).mul_right M).mul_right (s.τ i^z))
  have he := inside_infinite (f:=f) (U:=U) (fun z (_:z≤k)=>(hs z).summable) ?H hl hv
  exact ⟨he.1,he.2.1,he.2.2.trans_eq (hs _).tsum_eq⟩
  case H =>
    filter_upwards [hh,hh.eventually_nhds] with V hV h'
    have hpow (d : ℕ) := ((hV.coeff W).neg.pow (d+1))
    have hM := hV.has; have hp := (q_widths (p:=p) (s:=s) (N:=N) (k:=k) hM).2; have hx := hp.trans hr
    have hb' := hV.cash.mono (show 2*spare p≤p.speed by linarith only [four_spare p,spare_pos p]) le_rfl
    have hu := hV.space (r:=2*spare p) (by linarith only [spare_pos p])
    refine ⟨fun l _ _=>Measurable.of_discrete.aestronglyMeasurable,fun l hl hv d _ => ?_, fun l hl hv e hd d _=> ((hpow d).prod hV.good).has hl e i j⟩
    exact (((hV.power_cost W hb hr (h'.mono fun _ hz => hz.base.symm) d).product hb' (hpow d) hV.good hu (by positivity) hM l hl hv).1.entry (hu.trans (s.width_le _ _ _ hl)) i j)
end YM.Further.CurvedGaussianJets.Jets
