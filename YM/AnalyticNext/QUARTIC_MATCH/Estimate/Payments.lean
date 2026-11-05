import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Numbers
import YM.Next.FREE_KERNELS.Amend

/-!
# Per-site jets of the input and output path functionals

Before channels. Differentiate the TRUE exponential and unmasked sum. Input-base
rows paid independently from R3 and R4 (reservation before L).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n l : Side} {ι α : Type*} [DecidableEq ι] {k : ℕ}
open Purse Logfee Plaque Cargo
variable {P : Purse ι (Site n)} {η C σ τ R : ℝ}
namespace Village

def formed (W : PathData G) (p : PlaqAxes) (x : Site n) (z : Dir G n) := W.ell (represent z) (x,p)
def expense (q : Clip) (W : PathData G) (p : PlaqAxes) (x : Site n) (z : Dir G n) := q.direct*G.price (faceValue (represent z) (x,p))+‖formed W p x z‖^2/2

lemma formed_rate {W : PathData G} {p : Clip} {σ C Λ} (h : W.Bounds p σ C Λ) (k : PlaqAxes) (x : Site n) (a : Dir G n) : ContDiffAt ℝ ω (formed W k x) a :=
    Work.F02.ell_contDiffAt (A:=represent) h (x,k) (fun _i => (represent_smooth ..).contDiffAt)
lemma exp_price (G : Gauge) (u : G.El) : G.price u = (2*G.colorScale^2)⁻¹ * ‖G.mat u-1‖^2 := by
  have he := G.colorScale_pos
  have hx := G.chord_price u
  rw [Gauge.chord] at hx; change (‖G.mat u - 1‖ / G.colorScale)^2 = _ at hx
  rw [inv_mul_eq_div,eq_div_iff]; swap; · positivity
  field_simp at hx; linarith
lemma expense_rate {W : PathData G} {p : Clip} {σ C Λ} (h : W.Bounds p σ C Λ) (k : PlaqAxes) (x : Site n) (a : Dir G n) :
    ContDiffAt ℝ ω (expense p W k x) a := by
  have he := formed_rate h k x a
  have hp := (order k x (G:=G)).contDiffAt (x:=a); unfold expense; simp_rw [exp_price]
  exact (contDiffAt_const.mul (contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp a hp))).add
    (((contDiff_norm_sq ℝ).contDiffAt.comp a he).div_const _)
lemma atend_rate (A : ℕ → Atom G k) (h : 0 < σ) (he : SumBudget (fun i => (A i).budget σ) C) (p : Site n) (x : Dir G n) : ContDiffAt ℝ ω (atend A p) x := by
  let E (M : Work.F02.Ambient G n) := ∑' i, Work.F02.atomExt (A i) p M
  have ht : ContDiffAt ℝ ω E (Work.F02.physical (represent x)) := ((Work.F02.atomExt_series h he p (represent x)).contDiffAt).restrict_scalars ℝ
  have hh : atend A p=Complex.reCLM ∘ E ∘ fun x => Work.F02.physical (represent x) := by
    funext i; simp only [Function.comp_apply]
    unfold E; rw [Work.F02.atomExt_real h he]; rfl
  rw [hh]; exact Complex.reCLM.contDiff.contDiffAt.comp x (ht.comp x
    (Work.F02.physical_contDiffAt (A:=represent) fun i => (represent_smooth ..).contDiffAt))

lemma formed_budget {W : PathData G} {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 < η)
    (a : Dir G n) (ha : ‖a‖ < 1) (S : Finset ι) (m : ℕ) (hm : S.card ≤ m) (hq : 5*m*η ≤ σ*l.val)
    (C : ℝ) (hb : ∀ q : PlaqAxes, ∀ T⊆S, P.Jets T d (plasty q) a C)
    (q : PlaqAxes) (hc : 0 ≤ C) (hσ : 0 < σ) (hx : SumBudget (fun i => |(W.row q i).1| * Real.exp (σ * (W.row q i).2.length)) R) :
    P.Jets S d (formed W q) a (mailCharge G η m*C*R) := by
  let k := mailCharge G η m*C; have hk : 0 ≤ k := mul_nonneg (mailCharge_pos ..).le hc
  let f i := (W.row q i).1; let g i := (W.row q i).2
  let u (i : ℕ) (x : Site n) (a : Dir G n) := service W (x,q) i a
  let w (i : ℕ) := |f i| * Real.exp (σ*(g i).length)
  have hT (i) : P.Jets S d (u i) a (k*w i) := by
    let s := g i
    have he := spool_pays h he hp _ hm a ha.le s _ (hb s.plaq)
    apply (Jets.rate he (f i) (fun i => (spinner ..).contDiffAt)).mono
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (fee_limit _ hq) hk) (abs_nonneg _)).trans_eq (show _ = k*(|f i| *Real.exp (σ*s.length)) by ring)
  have hg (i : Site n) := reception W (i,q) hx hσ a ha d S
  unfold Jets
  rw [show (fun i => bill S d (formed W q i) a)=(fun i => ∑' j, bill S d (u j i) a) from funext fun i => (hg i).tsum_eq.symm]
  apply (Pays.tsum hT (hx.2.1.mul_left _) (fun i => (hg i).summable)).mono
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hx.2.2 hk

def baseCash (G : Gauge) (i : ℕ) (η r R : ℝ) := r*((2*G.colorScale^2)⁻¹*(2:ℝ)^i) + (1/2:ℝ)*(2:ℝ)^i*(mailCharge G η i*R)^2

lemma base_card {W : PathData G} {p : Clip} {d : ι→Dir G n} {τ E Λ} (hW : W.Bounds p τ E Λ)
    (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 < η)
    (a : Dir G n) (ha : ‖a‖ < 1) (S : Finset ι) (m : ℕ) (hm : S.card ≤ m) (hq : 5*m*η ≤ σ*l.val)
    (C : ℝ) (hb : ∀ q : PlaqAxes, ∀ T⊆S, P.Jets T d (plasty q) a C)
    (q : PlaqAxes) (hc : 0 ≤ C) (hσ : 0 < σ) (hx : SumBudget (fun i => |(W.row q i).1| * Real.exp (σ * (W.row q i).2.length)) R) :
    P.Jets S d (expense p W q) a (baseCash G m η p.direct R*C^2) := by
  let f := plasty q (n:=n) (G:=G)
  let g := formed W q (n:=n)
  let k := p.direct*(2*G.colorScale^2)⁻¹
  have hG := G.colorScale_pos; have hk : 0 ≤ k := mul_nonneg p.quadratic_pos.le (by positivity)
  have hf (i) := (order (G:=G) q i).contDiffAt (x:=a)
  have hU (i) := formed_rate hW q i a
  have hh (B) (hB : B⊆S) := formed_budget h he hp a ha B m ((Finset.card_le_card hB).trans hm) hq C
    (fun q i hi => hb q i (hi.trans hB)) q hc hσ hx
  let F i z := (innerSL ℝ) (f i z) (f i z)
  let V i z := (innerSL ℝ) (g i z) (g i z)
  have hA (i) : ContDiffAt ℝ ω (F i) a := (((innerSL ℝ).contDiff.contDiffAt.comp _ (hf i)).clm_apply (hf i))
  have hB (i) : ContDiffAt ℝ ω (V i) a := (((innerSL ℝ).contDiff.contDiffAt.comp _ (hU i)).clm_apply (hU i))
  have he1 := Jets.rate (f:=F) (Jets.priced _ (fun x y => norm_inner_le_norm x y) hf hf (hb q) (hb q) m hm) k hA
  have he2 := Jets.rate (f:=V) (Jets.priced _ (fun x y => norm_inner_le_norm x y) hU hU hh hh m hm) (1/2:ℝ) hB
  have hr : expense p W q (n:=n)=fun i z => k • F i z+(1/2:ℝ) • V i z := by
    funext i z
    simp only [expense,exp_price]; change p.direct*((2*G.colorScale^2)⁻¹*‖f i z‖^2)+‖g i z‖^2/2=k*inner ℝ (f i z) (f i z)+ (1/2:ℝ)*inner ℝ (g i z) (g i z)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]; unfold k; ring
  rw [hr]; apply (Jets.adding (fun i => (hA i).const_smul k) (fun i => (hB i).const_smul (1/2:ℝ)) he1 he2).mono (le_of_eq ?_)
  rw [abs_of_nonneg hk,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ))]
  unfold baseCash k; ring

lemma atom_budget {κ : ℕ} (A : ℕ→Atom G κ) {d : ι→Dir G n} (h : Linkbill l P d) (he : tollRate P l η) (hp : 0 < η)
    (a : Dir G n) (ha : ‖a‖ < 1) (S : Finset ι) (m : ℕ) (hm : S.card ≤ m) (hq : 5*m*η ≤ σ*l.val)
    (C : ℝ) (hb : ∀ q : PlaqAxes, ∀ T⊆S, P.Jets T d (plasty q) a C)
    (hc : 0 ≤ C) (hσ : 0 < σ) (hx : SumBudget (fun i => (A i).budget σ) R) :
    P.Jets S d (atend A) a (((2:ℝ)^m*(mailCharge G η m*C))^κ*R) := by
  let v := ((2:ℝ)^m*(mailCharge G η m*C))^κ
  have hv : 0 ≤ v := by unfold v; have ht := mailCharge_pos G η m; positivity
  have he (i) := levy h he hp a ha.le S m hm hq _ hb (A i) hc
  have hi (i : Site n) := application A a ha hσ hx i S d
  unfold Jets; rw [show (fun i => bill S d (atend A i) a)=(fun i => ∑' j, bill S d (effect (A j) i) a) from funext fun i => (hi i).tsum_eq.symm]
  apply (Pays.tsum he (hx.2.1.mul_left _) (fun i => (hi i).summable)).mono
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hx.2.2 hv

lemma start_zero {κ : ℕ} (A : ℕ→Atom G κ) {d : ι→Dir G n} (S : Finset ι) (hm : S.card < κ) (hp : 0<σ) (hx : SumBudget (fun i => (A i).budget σ) R) :
    P.Jets S d (atend A) 0 0 := by
  unfold Jets; rw [show (fun i => bill S d (atend A i) 0)=(0:Site n→ℝ) from funext fun i => by
    rw [← (application A (0:Dir G n) (by simp) hp hx i S d).tsum_eq]; simp_rw [submissing _ _ _ _ hm,tsum_zero]; rfl]
  exact Pays.zero le_rfl
end Village
end YM.AnalyticNext.QuarticMatch.Estimate
