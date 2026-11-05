import YM.AnalyticNext.QUARTIC_MATCH.Pre.Accounting
import YM.AnalyticNext.QUARTIC_MATCH.Pre.GaugeDir
import YM.Work.B04

/-!
# Flat centered Hessian and installed solution

Use HERE the actual `Inputs` (A0 relation). Reduce the quantitative problem to
pricing a bilinear completion on this exact branch; no change of F03/04
input and output witnesses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Pre
open Filter Function Lattice RG Wilson Precision Push Bid Exterior Bloch Matrix Tree Work.F03 Work.F04
open Joint Knot
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
namespace Centered
variable {G : Gauge} {c f : Side}
local notation "Y" => Vertical G c f
local notation "Z" => JointSpace G c f

variable (S : StepData c f) (t : S.Choices) (h : S.patch.Branches S.kernel G)

def debt (z : Z) := z.1 - firstT S z.2.1 + gradient z.2.2

def discrepancy (z : Z) (e : Edge (Site c)) := represent z.1 e * (Lattice.gauge (power z.2.2) (send S t z.2.1) e)⁻¹
def second (B : Bed) (z w : Z) := gaugeFiscal B z.2.1 w.2.1 + S.kernel.penalty *
    ∑ i : Body 1 c, inner ℝ (debt S z i) (debt S w i)

def secondOne (B : Bed) (a k : form 1 f) (u v : form 0 c) :=
    dotProduct a (Precision.K (B.metric.acts f) *ᵥ k) + S.kernel.penalty *
      dotProduct (Precision.mean S *ᵥ a - d 0 c *ᵥ u) (Precision.mean S *ᵥ k - d 0 c *ᵥ v)
lemma parts_debt (z : Z) (j : G.ColorIndex) : parts G 1 (debt S z) j = parts G 1 z.1 j - Precision.mean S *ᵥ parts G 1 z.2.1 j+d 0 c *ᵥ sitePart z.2.2 j := by rw [← parts_grad]; rfl
lemma pairs (B : Bed) (z w : Y) : second S B (0,z) (0,w) = ∑ j : G.ColorIndex,
    secondOne S B (parts G 1 z.1 j) (parts G 1 w.1 j) (sitePart z.2 j) (sitePart w.2 j) := by
  rw [second, counting_inner,gaugeFiscal,Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [parts_debt S _ i, secondOne]
  rw [show parts G 1 (0:Dir G c) i=0 from rfl, zero_sub,zero_sub]
  rw [show -_+_ = -(Precision.mean S *ᵥ parts G 1 z.1 i-d 0 c *ᵥ sitePart z.2 i) by abel,
    show -_+_ = -(Precision.mean S *ᵥ parts G 1 w.1 i-d 0 c *ᵥ sitePart w.2 i) by abel, neg_dotProduct, dotProduct_neg, neg_neg]

section
include h
lemma born (e : Edge (Site c)) : discrepancy S t (0:Z) e=1 := by
  simp only [discrepancy, Prod.snd_zero, Prod.fst_zero, power_zero, send_zero S h, Joint.trivial,link_one,Pi.one_apply,inv_one,mul_one]
lemma priced (e : Edge (Site c)) : Smooth (0:Z) (fun z => discrepancy S t z e) := by
  apply Smooth.mul (Q:=fun z : Z => represent z.1 e) (V:=fun z => (Lattice.gauge (power z.2.2) (send S t z.2.1) e)⁻¹)
  · exact (represent_smooth (G:=G) e).contDiffAt.comp (f:=Prod.fst) (0:Z) contDiffAt_fst
  have he (x : Site c) : Smooth (0:Z) (fun z => power z.2.2 x) := (power_jet (G:=G) x).comp (f:=fun z : Z => z.2.2) (0:Z) (by fun_prop)
  have hh : Smooth (0:Z) (fun z => send S t z.2.1 e) := (send_smooth S h t e).comp (f:=fun z : Z => z.2.1) (0:Z) (by fun_prop)
  exact (((he _).mul hh).mul (he _).inv).inv
lemma price_rate (z : Z) (e : Edge (Site c)) : HasDerivAt (fun s : ℝ => G.mat (discrepancy S t (s • z) e))
    (G.colorMat (debt S z (e.1,coord e.2))) 0 := by
  have hi (s : ℝ) : power (s • z).2.2=power (s • z.2.2) := rfl
  have ha := ((power_rate z.2.2 e.1).mul (send_rate S h t e z.2.1)).mul (power_rate z.2.2 (e.1+step e.2)).star
  unfold discrepancy; simp_rw [hi,Lattice.gauge,G.mat_mul,G.mat_inv]
  convert! (represent_rate z.1 e).mul ha.star using 1
  simp only [debt,Pi.mul_apply,zero_smul,link_one,power_zero,send_zero S h,G.mat_one,
    Pi.one_apply,mul_one,one_mul,star_add,star_one,G.colorMat_skew,gradient, Pi.add_apply,Pi.sub_apply,
    show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _,map_add,map_sub,star_neg]
  abel

lemma limit_pay (z : Z) (e : Edge (Site c)) : Tendsto (fun s : ℝ => G.price (discrepancy S t (s • z) e) / s^2)
    (𝓝[≠] 0) (𝓝 (inner ℝ (debt S z (e.1,coord e.2)) (debt S z (e.1,coord e.2)) / 2)) := by
  rw [real_inner_self_eq_norm_sq]; exact price_limit (V:=fun s => discrepancy S t (s • z) e) (by rw [zero_smul]; exact born S t h e) (price_rate S t h z e)
variable {p : Clip} {W : PathData G} {σ C Λ u v : ℝ} {B : Bed}
lemma principal (hP : W.Bounds p σ C Λ) (ht : Attached B W) (hf : Floor B p f u v) (hs : Sworn B f G)
    (z : Z) : Tendsto (fun s : ℝ => cash S t p W (s • z) / s^2) (𝓝[≠] 0) (𝓝 (second S B z z / 2)) := by
  simp_rw [cash,second,groupEnergy,add_div,mul_div_assoc, Finset.sum_div,
    ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv) (fun i => inner ℝ (debt S z i) (debt S z i)/2)]
  exact ((main_limit hP ht hf hs z.2.1).add ((tendsto_finsetSum Finset.univ fun i _ => limit_pay S t h z i).const_mul _))

lemma reveals (hP : W.Bounds p σ C Λ) (ht : Attached B W) (hf : Floor B p f u v) (hs : Sworn B f G)
    (hh : ContDiffAt ℝ ω (cash S t p W) 0) : cash S t p W 0 = 0 ∧ fderiv ℝ (cash S t p W) 0 = 0 ∧
    ∀ x y, iteratedFDeriv ℝ 2 (cash S t p W) 0 ![x,y] = second S B x y := by
  apply hessian_of_limit (hh.of_le le_top) (principal S t h hP ht hf hs)
  · intro x y z
    have he : debt S (x+y)=debt S x+debt S y := by
      ext i j; change parts G 1 (debt S (x+y)) j i=_
      rw [parts_debt]
      change (_:ℝ)= parts G 1 (debt S x) j i+parts G 1 (debt S y) j i
      rw [parts_debt,parts_debt]; simp only [Prod.fst_add, Prod.snd_add, parts_add,
        show sitePart (x.2.2+y.2.2) j=sitePart x.2.2 j+sitePart y.2.2 j from rfl, Matrix.mulVec_add, Pi.add_apply,Pi.sub_apply]; abel
    simp only [second,Prod.snd_add,Prod.fst_add,gaugeFiscal_add,he,Pi.add_apply,inner_add_left,
      Finset.sum_add_distrib,mul_add]; abel
  intro x y
  simp_rw [second, metric_pair B hP ht _ _ hf]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; rw [real_inner_comm (faceCurl _ x.2.1),real_inner_comm (ellLine W _ x.2.1)]
  congr 1; apply Finset.sum_congr rfl; intro i _; exact real_inner_comm ..
end

def stance (U : Matrix (Body 1 f) (Body 1 c) ℝ) : Dir G c→L[ℝ] Y :=
    LinearMap.toContinuousLinearMap {
      toFun := fun x => (fun i => WithLp.toLp 2 (fun j => (U *ᵥ parts G 1 x j) i),0)
      map_add' := fun x y => Prod.ext (funext fun i => by simp [parts_add,Matrix.mulVec_add]; rfl) (by simp)
      map_smul' := fun s x => Prod.ext (funext fun i => by simp [mulVec_smul, show ∀ j, parts G 1 (s • x) j=s • parts G 1 x j from fun _ => rfl]; rfl) (by simp) }

lemma interest {B D : Bed} {U} (hk : Inputs S U (B.metric.acts f) (D.metric.acts c))
    (x : Dir G c) (z : Z) : second S B z (x,stance U x)=gaugeFiscal D z.1 x := by
  have he (j : G.ColorIndex) : parts G 1 (stance U x).1 j=U*ᵥ parts G 1 x j := rfl
  have hh (j : G.ColorIndex) : parts G 1 (debt S (x,stance U x)) j=S.kernel.penalty⁻¹ • (Precision.K (D.metric.acts c) *ᵥ parts G 1 x j) := by
    rw [parts_debt,he]
    dsimp only
    rw [mulVec_mulVec,hk.dual,sub_mulVec, one_mulVec,smul_mulVec,
      show sitePart (stance U x).2 j=0 from rfl, mulVec_zero]; simp
  rw [second,counting_inner]; unfold gaugeFiscal; rw [Finset.mul_sum,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [he, hh,mulVec_mulVec,hk.primal, ← mulVec_mulVec, dotProduct_mulVec,vecMul_transpose,dotProduct_smul,
    smul_eq_mul,← mul_assoc,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_mul,parts_debt, add_dotProduct, sub_dotProduct]
  have hy : dotProduct (d 0 c *ᵥ sitePart z.2.2 j) (Precision.K (D.metric.acts c) *ᵥ parts G 1 x j)=0 := by
    rw [← vecMul_transpose (d 0 c), ← dotProduct_mulVec, mulVec_mulVec,K_orthogonal]; simp
  rw [hy]; abel

section use
variable {I : Type*} [NormedAddCommGroup I] [InnerProductSpace ℝ I] [FiniteDimensional ℝ I] [CompleteSpace I]
    {T : Forest S.ratio} {p : Clip} {W : PathData G} {b : Dir G c→AxisChart G T} {σ C Λ η u v : ℝ} {B D : Bed}
include h
/-- Invoice reduction to Hessian pair with the actual `K S`.
Stationary WITH prescribed tangent on all B; `OnShell.equation` permits
pairing against rough probes with pre-L estimates. -/
theorem purchase (hP : W.Bounds p σ C Λ) (hb : Critical T p W b) (ht : Attached B W) (hf : Floor B p f u v)
    (hs : Sworn B f G) {U} (hk : Inputs S U (B.metric.acts f) (D.metric.acts c)) (hv : Comptroller T B p W)
    (he : 0 < η) (hq : PriceGap T p W η)
    (q : Y→L[ℝ] I) (H : ∀ v : Y,v≠0 → 0 < second S B (0,v) (0,v)+inner ℝ (q v) (q v))
    (hp : Surjective (q ∘ depart S)) : ∃ a : Dir G c → Y,a 0=0 ∧ OnShell (cash S t p W) a 0 ∧
      fderiv ℝ a 0=stance U ∧ (∀ u w, q (D2 a 0 u w)=0) ∧ cash S t p W ∘ arc a =ᶠ[𝓝 0] Joint.value T t p W b := by
  have hh := starts S t h hP hb
  have hu := reveals S t h hP ht hf hs hh
  have hb' (x : Dir G c) (y : Y) : D2 (cash S t p W) 0 (x,stance U x) (0,y) = 0 := by
    rw [hh.isSymmSndFDerivAt_of_omega ..,← D2_jet, hu.2.2,interest _ hk]; simp [gaugeFiscal,parts,dotProduct]
  obtain ⟨a,ha,hα,hβ,hH⟩ := draws (move S t (G:=G)) (moves_jet S t h) q (stance U) (fun y => by
    obtain ⟨u,hu⟩ := hp y; exact ⟨u,by rw [ContinuousLinearMap.comp_apply,move_rate S t h]; exact hu⟩) (move_null S t)
    (cash S t p W) hh (free_spin S t h hP) (by simp only [vert, hu.2.1,ContinuousLinearMap.zero_comp]) hb'
    (fun v hv => by rw [← D2_jet,hu.2.2]; exact H v hv)
  exact ⟨a,ha,hα,hβ,hH,buys S t h hP hb B hv he hq a hα ha⟩
end use
end Centered
end YM.AnalyticNext.QuarticMatch.Pre
