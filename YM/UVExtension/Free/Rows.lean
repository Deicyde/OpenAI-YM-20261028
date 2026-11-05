import YM.UVExtension.Limits
import YM.Next.FREE_KERNELS.Bank
import YM.Next.FREE_KERNELS.Lever
import YM.Extraction.Simultaneous

/-!
Compactness only as a proof of full-sequence limits. Uniqueness by discrete Fourier tests or other
uniqueness predicate on rows. Weighted width convergence, not just on each fixed input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension
open Extraction Function Lattice Laurent Bloch Filter RG Next.Free
open scoped Topology BigOperators Classical
-- handy use outside
lemma subseq_rule {X : Type*} [TopologicalSpace X] {R : ℕ→X} {W : X}
    (h : ∀ f : ℕ→ℕ, StrictMono f → ∃ g : ℕ →ℕ, StrictMono g ∧ Tendsto (R ∘ f ∘ g) atTop (𝓝 W)) :
    Tendsto R atTop (𝓝 W) := by
  apply tendsto_def.mpr
  intro S hs
  by_contra hp
  obtain ⟨f,hf,H⟩ := extraction_of_frequently_atTop (show ∃ᶠ i in atTop, R i∉ S by simpa [frequently_atTop] using hp)
  obtain ⟨g,hg,hh⟩ := h f hf
  obtain ⟨i,hi⟩ := (hh.eventually hs).exists
  exact H (g i) hi

namespace Free
variable {α β : Type*}

/-- Convergence tag with a working exponential width. `Widths` carry the finiteness and budget
 tests, so no undefined-tsum rates. -/
def Fell (η : ℝ) (R : ℕ→Row α β) (T : Row α β) :=
  ∀ ε > (0:ℝ), ∀ᶠ i in atTop, (R i-T).strip η ε

/-- Common analytic row control, includes convergence in *every* strict interior Width. -/
structure Received (R : ℕ→Row α β) (T : Row α β) (η C : ℝ) : Prop where
  bound : T.strip η C
  entries : Tendsto R atTop (𝓝 T)
  interior : ∀ γ, γ<η → Fell γ R T

variable {η C : ℝ} {R : ℕ→Row α β} {T U : Row α β}

section testers
variable (hf : Tendsto R atTop (𝓝 T)) (h : ∀ᶠ i in atTop, (R i).strip η C)
include hf h

omit hf h in
private lemma item_bound {f : Row α β} (h : f.strip η C) (x y z) :
    ‖f x y z‖ ≤ C * Real.exp (-η*size z) := by
  have he := h x y
  rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
  simpa using ((he.2.1.sum_le_tsum ({z} : Finset Cover) (fun i _=> he.1 i)).trans (h x y).2.2)

lemma read_entry (x y) {p : Momentum} (hp : physical p) (hη : 0<η) :
    Tendsto (fun i=> (R i).read p x y) atTop (𝓝 (T.read p x y)) := by
  let Z i z:= mode p z*((R i x y z:ℝ):ℂ)
  have he z : Tendsto (fun i=> Z i z) atTop (𝓝 (mode p z*(T x y z:ℂ))) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf x) y) z)).const_mul _
  refine tendsto_tsum_of_dominated_convergence (((Width.compactPay η hη).2.1).mul_left C) he (h.mono fun i hi z=>?_)
  dsimp only [smul_eq_mul]; rw [norm_mul,mode_real p z hp,one_mul, Complex.norm_real]; exact item_bound hi x y z

lemma acts_entry (n : Side) (x y) (hη : 0<η) :
    Tendsto (fun i=> (R i).acts n x y) atTop (𝓝 (T.acts n x y)) := by
  let f (A : Row α β) (x:Site n × α) (y : Site n×β) z := if y.1=x.1+wrap n z then A x.2 y.2 z else 0
  have he (x : Site n × α) (y : Site n × β) z : Tendsto (fun i=> f (R i) x y z) atTop (𝓝 (f T x y z)) := by
    unfold f; split_ifs
    · exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf _) _) _
    exact tendsto_const_nhds
  refine tendsto_tsum_of_dominated_convergence (((Width.compactPay η hη).2.1).mul_left C) (he x y) (h.mono fun i hi z=>?_)
  split
  · exact item_bound hi x.2 y.2 z
  exact (norm_zero.trans_le ((norm_nonneg _).trans (item_bound hi x.2 y.2 z)))

lemma inherits : T.strip η C := by
  intro x y
  let t z:= Real.exp (η*size z)*‖T x y z‖
  have hh z:0 ≤ t z:=by unfold t; positivity
  have hP (s:Finset Cover) : ∑ i∈s,t i ≤ C := by
    let f i:= ∑ z∈s, Real.exp (η * size z)*‖R i x y z‖
    have ht : Tendsto f atTop (𝓝 (∑ i∈s,t i)) :=
      tendsto_finsetSum s fun z _=> (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf _) _) z).norm.const_mul _
    exact le_of_tendsto ht (h.mono fun i hi=> ((hi x y).2.1.sum_le_tsum _ (fun z _=> (hi x y).1 z)).trans (hi x y).2.2)
  have ht:= summable_of_sum_le hh hP
  exact ⟨hh,ht,ht.tsum_le_of_sum_le hP⟩

lemma reported [Fintype α] [Fintype β] : Received R T η C := by
  refine ⟨inherits hf h, hf,fun γ hg ε hε => eventually_all.mpr fun x=> eventually_all.mpr fun y=>?_⟩
  let t i z:= Real.exp (γ*size z)*‖(R i-T) x y z‖
  have hh i z : 0 ≤ t i z:= mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have ht z:Tendsto (fun i=> t i z) atTop (𝓝 0) := by
    have hK:= (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf x) y) z).sub_const (T x y z)
    simpa only [sub_self,norm_zero,mul_zero] using! hK.norm.const_mul (Real.exp (γ*size z))
  let b z:= (C+C)*Real.exp (-(η-γ)*size (z:Cover))
  have hS : Summable b:= ((Width.compactPay (η-γ) (sub_pos.mpr hg)).2.1).mul_left _
  have hv : ∀ᶠ i in atTop, ∀ z, ‖t i z‖ ≤ b z := by
    filter_upwards [h] with i hi z
    rw [Real.norm_of_nonneg (hh i z)]
    apply (mul_le_mul_of_nonneg_left ((norm_sub_le (R i x y z) (T x y z)).trans (add_le_add
        (item_bound hi x y z) (item_bound (inherits hf h) x y z))) (Real.exp_pos (γ*size z)).le).trans_eq
    unfold b; rw [← add_mul,mul_left_comm,← Real.exp_add]; congr 2; ring
  have hZ : Tendsto (fun i=> ∑' z,t i z) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hS ht hv
  filter_upwards [hv,hZ.eventually_le_const hε] with i hi hx
  exact ⟨hh i,hS.of_norm_bounded hi,hx⟩
end testers
variable [Fintype α] [Fintype β]

-- Matrix.norm instance-free pointwise version
omit [Fintype α] [Fintype β] in
lemma read_limit (h : Received R T η C) (hB : ∀ᶠ i in atTop,(R i).strip η C) (hη : 0<η) {p : Momentum} (hp : physical p) :
    Tendsto (fun i=> (R i).read p) atTop (𝓝 (T.read p)) := by
  exact tendsto_pi_nhds.mpr fun x=> tendsto_pi_nhds.mpr fun y=> read_entry h.entries hB x y hp hη

omit [Fintype α] [Fintype β] in
lemma acts_limit (h : Received R T η C) (hB : ∀ᶠ i in atTop,(R i).strip η C) (hη : 0<η) (n : Side) :
    Tendsto (fun i=> (R i).acts n) atTop (𝓝 (T.acts n)) := by
  exact tendsto_pi_nhds.mpr fun x=> tendsto_pi_nhds.mpr fun y=> acts_entry h.entries hB n x y hη

lemma row_extract (h : ∀ᶠ i in atTop,(R i).strip η C) : ∃ f : ℕ → ℕ, StrictMono f ∧
    ∃ T : Row α β, Received (R ∘ f) T η C := by
  let I := α × β × Cover
  let B (x:I) := Metric.closedBall (0:ℝ) (C * Real.exp (-η*size x.2.2))
  have hk : Countable I:=inferInstanceAs (Countable (α × β × Cover))
  obtain ⟨f,y,ht⟩:= simultaneous (fun (i:I) n=> R n i.1 i.2.1 i.2.2) (K:=B) (fun _=>isCompact_closedBall ..)
    (fun i=> h.mono (fun k h=>Metric.mem_closedBall.mpr ((dist_zero_right _).trans_le (item_bound h i.1 i.2.1 i.2.2))))
  refine ⟨f.choose,f.monotone,(fun a b c=> y (a,b,c)),?_⟩
  exact reported (tendsto_pi_nhds.mpr fun x=> tendsto_pi_nhds.mpr fun z=> tendsto_pi_nhds.mpr fun u=>
    (ht (x,z,u)).2) (f.cofinal.eventually h)

lemma row_all (h : ∀ᶠ i in atTop,(R i).strip η C) (hp : ∀ (f g : ℕ→ℕ), StrictMono f → StrictMono g →
    ∀ x y, Received (R ∘ f) x η C → Received (R ∘ g) y η C → x=y) : ∃ x, Received R x η C := by
  obtain ⟨f,hf,x,hx⟩:=row_extract h; refine ⟨x,reported (subseq_rule ?_) h⟩
  intro u hu
  obtain ⟨g,hg,y,hy⟩:=row_extract (show ∀ᶠ i in atTop, ((R ∘ u) i).strip η C from hu.tendsto_atTop.eventually h)
  have hr:=hp (u∘g) f (hu.comp hg) hf y x hy hx
  exact ⟨g,hg,hr ▸ hy.entries⟩

lemma heard_unique (h : T.strip η C) (hU : U.strip η C) (hη : 0<η) (hv : ∀ p∈baseCube, p≠0 → T.read p=U.read p) : T=U := by
  have hT : Whole T:=⟨_,_,hη,h⟩
  have hU' : Whole U:=⟨_,_,hη,hU⟩
  apply bank_injective hT.safe hU'.safe
  apply acts_of_cube hT.safe hU'.safe
  intro p hp
  -- renew law in Lever is universe constrained; use entry functions
  ext x y
  let f q := T.read q x y
  let g q := U.read q x y
  change f p = g p
  refine renew_q f g 0 ?_ ?_ (fun q hq hv'=>?_ ) p hp
  · intro q hq; exact continuousAt_pi.mp (continuousAt_pi.mp (read_here T hT hq) x) y
  · intro q hq; exact continuousAt_pi.mp (continuousAt_pi.mp (read_here U hU' hq) x) y
  apply congr_fun (congr_fun (hv q hq ?_) x) y
  rintro rfl
  rw [Exterior.q] at hv'; simp at hv'


lemma row_at_puncture (h : ∀ᶠ i in atTop,(R i).strip η C) (hη : 0<η) (hp : ∀ p∈baseCube, p≠0 → Arrives (fun i=> (R i).read p)) :
    ∃ x, Received R x η C := by
  apply row_all h; intro f g hf hg T U hT hU; apply heard_unique hT.bound hU.bound hη
  intro p hb hn
  obtain ⟨t,ht⟩ := hp p hb hn
  exact (tendsto_nhds_unique (read_limit hT (hf.tendsto_atTop.eventually h) hη hb.1) (ht.comp hf.tendsto_atTop)).trans
    (tendsto_nhds_unique (read_limit hU (hg.tendsto_atTop.eventually h) hη hb.1) (ht.comp hg.tendsto_atTop)).symm
end Free
end YM.UVExtension
