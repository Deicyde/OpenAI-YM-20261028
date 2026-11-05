import YM.Further.CURVED_GAUSSIAN_JETS.Chains
import YM.Further.CURVED_GAUSSIAN_JETS.LocalJets
import YM.Further.CURVED_GAUSSIAN_JETS.Payment

/-!
# Left derivatives of true real Panel lines from integrable resolvents
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

lemma share_flow (l : Word G c) (f : ℝ → Word G c → Word G c → Table I)
    (h : ∀ x y : Word G c,x.length+y.length=l.length → Smooth fun u=> f u x y) : Smooth (fun u=> share l (f u)) := by
  induction l generalizing f with
  | nil => exact h [] [] rfl
  | cons d l ih => exact ih _ fun x y he i j=> (h (d::x) y (by simp; omega) i j).add (h x (d::y) (by simp; omega) i j)

def Flow (A : ℝ → Field G c I) (U : Config G c) (k : ℕ) := ∀ l : Word G c, l.length≤k → Smooth fun u=>jet l (A u) U
namespace Flow
variable {A B : ℝ → Field G c I}

lemma neg (ha : Flow A U k) : Flow (fun u V=>-(A u V)) U k := by
  intro l hl; simp only [jet_neg]; exact fun i j=>(ha l hl i j).neg
lemma diff (ha : Flow A U k) (hb : Flow B U k) (h : ∀ u : ℝ,0<u → Good (A u) k U ∧ Good (B u) k U) :
    Flow (fun u V=> A u V - B u V) U k := fun l hl i j => ((ha l hl i j).sub (hb l hl i j)).congr fun u hu=> congr_fun (congr_fun (jet_minus (h u hu).1 (h u hu).2 hl) i) j
lemma prod (ha : Flow A U k) (hb : Flow B U k) (h : ∀ u : ℝ,0<u → Good (A u) k U ∧ Good (B u) k U) :
    Flow (fun u V=> A u V * B u V) U k := fun l hl i j => ((share_flow l _ (fun x y he=> (ha x (by omega)).mul (hb y (by omega)))) i j).congr fun u hu=>
      congr_fun (congr_fun (jet_prod (h u hu).1 (h u hu).2 hl) i) j
lemma pow (ha : Flow A U k) (hg : ∀ u : ℝ,0<u → Good (A u) k U) (j : ℕ) : Flow (fun u V => (A u V)^j) U k := by
  induction j with
  | zero => simp only [pow_zero]; exact fun _ _ _ _=>continuousOn_const
  | succ j ih => simp only [pow_succ]; exact ih.prod ha (fun u hu=>⟨(hg _ hu).pow _,hg _ hu⟩)
end Flow

variable (h : Street p s k Q A U M)
include h
lemma Street.raise_flow : Flow (raise A) U k := by
  intro l hl
  rcases eq_or_ne l [] with rfl|hh
  · simp only [jet_nil]; exact fun i j => (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
  simp only [jet_raise h.good _ hl hh]; exact fun _ _ => continuousOn_const
lemma Street.eye_flow : Flow (Jets.eye A) U k := by
  suffices ∀ j : ℕ, j ≤ k → Flow (Jets.eye A) U j from this _ le_rfl
  intro j hj; induction j with
  | zero => rintro l hl; simp only [List.length_eq_zero_iff, Nat.le_zero] at hl; subst l
            exact Line.inv_cont h.base.pos
  | succ j ih =>
    intro l hl; specialize ih (by omega)
    by_cases he : l.length ≤ j; · exact ih l he
    induction l using List.reverseRecOn with
    | nil => simp at he
    | append_singleton l d _ =>
      let f u := jet [d] (raise A u)
      have he : l.length=j := by simp at he hl; omega
      have hD (u) := (h.good.raise u).jet (l:=[d]) (m:=j) (by simp; omega)
      have hf : Flow f U j := by
        intro l hl; simp only [f,iter]; exact h.raise_flow _ (by simp; omega)
      have hE u hu := (Street.eye h (u:=u) hu).lower (Nat.le_of_succ_le hj)
      have hh := (ih.prod hf fun u hu=>⟨hE u hu.le,hD u⟩).prod ih fun u hu=>⟨(hE u hu.le).prod (hD u), hE u hu.le⟩
      intro i j; exact ((hh l he.le i j).neg).congr fun u hu=> congr_fun (congr_fun (jet_eye (h.good.lower (by omega)) d u (l:=l) (h.base.shift_pos (le_of_lt hu)).isUnit) i) j

lemma Street.column_flow : Flow (Jets.probe W A) U k := by
  intro l hl i j; by_cases hh : i∈W.box j
  · simp only [jet_probe W i j hh]; exact (h.slab W j).eye_flow _ hl _ _
  simp only [jet,of_apply,Jets.probe,Windows.column,dif_neg hh]; exact continuousOn_const
lemma Street.defect_flow : Flow (Jets.err W A) U k := ((h.raise_flow.prod (h.column_flow W) fun u hu=>⟨h.good.raise u,h.probe W hu.le⟩)).diff (fun _ _ _ _=> continuousOn_const)
    (fun u hu=>⟨(h.good.raise u).prod (h.probe W hu.le), Good.const _⟩)

omit h in
lemma cash_one {s : Weights a} {r : ℝ} : Cash (G:=G) (c:=c) s r k Q U (fun _=> (1:Table I)) 1 := by
  intro l hl hd; rw [jet_const]; split <;> rename_i he; subst l; exact Weights.zero_order Rows.one; exact Weights.zero zero_le_one
omit h in
lemma cash_diff_one (hr : Cash s p.speed k Q U A M) (hg : Good A k U) : Cash s p.speed k Q U (fun V => A V - 1) (M+1) :=
    hr.plus cash_one.neg hg (Good.const (-1))

def dose (A : Field G c I) (i : I) (u : ℝ) (U : Config G c) := Line.dose (A U) i u

def dose_cost (p : Prices) (s : Weights a) (k : ℕ) (M : ℝ) := s.pay k*discount p s k M k*(M+1)

lemma dose_terms (i : I) : Terms (volume.restrict (Ioi 0)) (Ioi 0) Q (dose A i) k (fun j u => Line.bell u*(dose_cost p s k M*s.τ i^j)) U := by
  let g (u : ℝ) V := of (fun x y : I=> (1+u)⁻¹) - eye A u V
  have hg {u : ℝ} (hu : 0<u) : Good (g u) k U := (Good.const _).minus (h.eye hu.le)
  have ht : Flow g U k := by
    apply Flow.diff _ h.eye_flow (fun u hu=>⟨Good.const _,h.eye hu.le⟩)
    rintro l hl; simp only [jet_const]; split
    · exact fun i j=> (continuousOn_const.add continuousOn_id).inv₀ fun u hu=> by dsimp; linarith [(show 0<u from hu)]
    exact fun i j=>continuousOn_const
  refine ⟨fun l hl hd=> (ht l hl i i).aestronglyMeasurable measurableSet_Ioi,fun l hl hd u hu=> ?_, fun l hl hd d hq u hu=> (hg hu).has hl d i i⟩
  have hv : 0<u := hu
  have he : IsUnit (shifted (A U) u) := (h.base.shift_pos hv.le).isUnit
  have hs : ∀ᶠ V in 𝓝 U, dose A i u V = ((1+u)⁻¹ • (eye A u V * (A V - 1))) i i := ((h.good.raise u).near_regular he).mono fun V hV=>by
    change IsUnit (shifted (A V) u) at hV
    have he : A V-1=shifted (A V) u - (1+u) • 1 := by rw [shifted,add_smul,one_smul]; abel
    unfold dose Line.dose eye; rw [he,Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hV),smul_sub,smul_smul, inv_mul_cancel₀ (by positivity : 0 < 1+u).ne',one_smul,Matrix.sub_apply, Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one]
  rw [left_on hs l]
  change ‖jet l (fun V=> (1+u)⁻¹ • _) U i i‖ ≤ _
  have hm := h.space (r:=p.speed) (by linarith only [spare_pos p,four_spare p]); have hM := h.has; have hp := discount_pos p s k hM k
  have hf := (eye_budget h hv.le le_rfl).product (cash_diff_one h.cash h.good) (h.eye hv.le) (h.good.minus (Good.const _)) hm (by positivity) (by positivity) l hl hd
  rw [jet_scale]
  exact ((hf.scale _).1.entry (hm.trans (s.width_le _ _ _ hl)) i i).trans_eq (by unfold Line.bell dose_cost; rw [abs_of_pos (by positivity),pow_two (1+u),one_div,mul_inv]; ring)

variable (hh : ∀ᶠ V in 𝓝 U, Street p s k Q A V M)
omit h
include hh

def price (A : Field G c I) (p : Prices) (i : I) (V : Config G c) := Panel.priceLine (A V) p.mass i
omit hh in
lemma price_eq (h : Street p s k Q A U M) (i : I) : price A p i U = total (volume.restrict (Ioi 0)) (dose A i) U := by
  have he := Panel.bill_quad h.base.symm h.base.numeric i
  exact (Line.dose_price h.base.pos p.gap_pos (he.1.trans he.2) h.base.numeric i).symm
lemma paid_dose (hl : l.length≤k) (hd : ∀ i∈l,Q i) (i : I) :
    leftDerivs (price A p i) l U = ∫ u : ℝ in Ioi 0, leftDerivs (dose A i u) l U ∧
      ‖leftDerivs (price A p i) l U‖ ≤ dose_cost p s k M*s.τ i^l.length ∧
      (∀ d l', l=d::l' → HasDerivAt (fun t : ℝ => leftDerivs (price A p i) l' (increment U (t • d))) (leftDerivs (price A p i) l U) 0) := by
  have he := hh.mono fun V hv => price_eq hv i
  have ht := hh.mono fun V hv => dose_terms hv i; have hm := ae_restrict_mem (μ:=volume (α:=ℝ)) (measurableSet_Ioi (a:=(0:ℝ)))
  have hx j (_ : j ≤ k) := Line.bell_int.1.mul_const (dose_cost p s k M*s.τ i^j)
  rw [left_on he l]; refine ⟨inside_total hm hx ht hl hd, (paid_total hm hx ht hl hd).trans_eq ?_, ?_⟩
  · rw [integral_mul_const,Line.bell_int.2,one_mul]
  intro d l rfl
  exact (live_total hm hx ht hl (fun i hi=> hd i (by simp [hi])) (hd d (by simp))).congr_of_eventuallyEq (((Multi.Puff.swing U d).eventually he.eventually_nhds).mono fun _ he=>left_on he l)
end YM.Further.CurvedGaussianJets.Jets
