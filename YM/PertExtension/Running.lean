import YM.Source.Construction
import YM.Extraction.Inherited
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Auxiliary inverse-coupling observation from the actual History. This
coupling is read from the represented action on the shot trajectory in its
band. Its leading equivalence DOES NOT identify a position coupling, or
estimate the diagrammatic remainder. Steps use the same `F.late` order as the
hierarchy. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension
open Filter Function Set Extraction RG Asymptotics
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

namespace Running
abbrev clock (C : Family G) := C.path.levels.clock
local notation "b₀" => (11*G.casimir/(48*Real.pi^ (2:ℝ)):ℝ)
lemma slope : G.slopeConstant=2*b₀ := by
  unfold Gauge.slopeConstant; simp [Real.rpow_two]; ring
private def cut (C : Family G)(N : ℕ)(t : ℕ×ℕ) : ℝ :=
  if t.2 ≤ N then C.path.β N t.1 t.2 else (clock C).hatBeta t.2

private lemma compact_diag (T : ℕ→Set ℝ) (hc : ∀ i,IsCompact (T i)) (cut0 : ℕ → ℕ×ℕ → ℝ) (hcut : ∀ N p m, cut0 N (p,m)∈T m) (f : Order) :
    ∃ g : Order,∃ B : ℕ→ℝ, ∀ m,(f.refine g).limits (fun _=>True) (fun N p=>cut0 N (p,m)) (B m) := by
  let S : Set ((ℕ × ℕ) → ℝ) := Set.pi univ (fun i=>T i.2)
  have hS : IsCompact S := isCompact_univ_pi (fun i=>hc i.2)
  obtain ⟨a,ha,φ,hφ,h⟩:= hS.tendsto_subseq (x:=fun k=>cut0 (f.mesh k)) (fun k p _=> hcut _ p.1 p.2)
  have he (k : ℕ) (m : ℕ) : a (f.per k,m)∈T m:= ha (f.per k,m) (mem_univ _)
  have hT : IsCompact (Set.pi univ T):= isCompact_univ_pi hc
  obtain ⟨y,-,ψ,hψ,hy⟩:= hT.tendsto_subseq (x:=fun k m=>a (f.per k,m)) (fun k i _=>he k i)
  let g : Order := ⟨⟨φ,hφ⟩,⟨ψ,hψ⟩⟩
  refine ⟨g,y,fun m=>⟨Eventually.of_forall (fun _=>trivial),fun p=>a (p,m),fun p _=>tendsto_pi_nhds.mp h (p,m),tendsto_pi_nhds.mp hy m⟩⟩

/-- Auxiliary refinement simultaneously extracting the scalar step histories at
all marks at and below the mesh. -/
lemma extraction (C : Family G) (h : C.Makes) (f : Order) : ∃ g : Order,
    ∃ B : ℕ→ℝ, ∀ m,(f.refine g).limits (fun _=>True) (fun N p=>C.path.β N p m) (B m) := by
  let T (m : ℕ) := Icc ((clock C).hatBeta m/2) (2*(clock C).hatBeta m)
  have ht (N) (p : ℕ × ℕ) : cut C N p ∈ T p.2 := by
    rcases le_or_gt p.2 N with hm|hn
    · rw [cut,if_pos hm]; exact (h.wilson.represents N p.1 p.2 hm).band
    rw [cut, if_neg hn.not_ge] -- cut here wrong simp?
    have he := C.path.levels.fits.delayed p.2
    exact ⟨by dsimp [clock];linarith only [he], by dsimp [clock];linarith only [he]⟩
  obtain ⟨g,y,H⟩:= compact_diag T (fun i=> isCompact_Icc) (cut C) (fun N p m=>ht N (p,m)) f
  refine ⟨g,y,fun m=> ?_⟩
  obtain ⟨ha,b,hb,hB⟩:= H m
  refine ⟨ha,b,fun p _=> ?_, hB⟩
  apply (hb p trivial).congr'
  filter_upwards [(f.refine g).mesh.cofinal.eventually (eventually_ge_atTop m)] with i hi
  change cut C _ (p,m) = _
  rw [cut,if_pos (show m ≤ _ from hi)]

variable (f : Order) (C : Family G)(h : C.Makes)(hG : G.Simple) {B : ℕ→ℝ}
def isLimit (C : Family G)(f : Order) (B : ℕ→ℝ) := ∀ m,Tendsto (fun z : ℕ×ℕ=>C.path.β z.1 z.2 m) f.fuse (𝓝 (B m))

variable (hB : isLimit C f B)
local notation "s" => C.S.scale

include hB h in
/-- Running retained at the common extraction. -/
lemma discrete : Tendsto (fun m=> B m / s m) atTop (𝓝 (2*b₀)) := by
  have he : Tendsto (fun m=> (B m - (clock C).hatBeta m)/s m) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]; intro ε hε
    have hh := h.wilson.running (ε/2) (by linarith)
    filter_upwards [hh,C.S.divergent.eventually (eventually_gt_atTop 0)] with m hm he
    have hz : ∀ᶠ z : ℕ×ℕ in f.fuse,
        |C.path.β z.1 z.2 m - (clock C).hatBeta m| ≤ ε/2 * s m := by
      rw [Order.fused,Order.late]; exact Eventually.of_forall fun k=>(f.mesh.cofinal.eventually (eventually_ge_atTop m)).mono (fun N hn=>hm _ _ hn)
    have hp : |B m - (clock C).hatBeta m| ≤ ε/2*s m := le_of_tendsto (((hB m).sub_const _).abs) hz
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (show 0<s m from he)]
    exact ((div_le_iff₀ he).mpr hp).trans_lt (by linarith only [hε])
  have hz := (he.add ((tendsto_const_nhds (x:=(clock C).bar)).div_atTop C.S.divergent)).add_const G.slopeConstant
  rw [zero_add,zero_add] at hz; rw [← slope]
  refine hz.congr' ?_
  filter_upwards [C.S.divergent.eventually (eventually_gt_atTop 0)] with i hi
  change (B i- _)/_+_/_+_= _
  change (B i- ((clock C).bar+_ * s i))/_+_/_+_= _
  field_simp
  ring

def choose (C : Family G) (μ : ℝ) : ℕ := Nat.find ((C.S.divergent.eventually (eventually_ge_atTop (Real.log μ))).exists)
lemma chosen (μ : ℝ) : Real.log μ ≤ s (choose C μ) := by have h : ∃ m, Real.log μ ≤ s m := ((C.S.divergent.eventually (eventually_ge_atTop (Real.log μ))).exists); exact Nat.find_spec h
lemma choosing : Tendsto (choose C) atTop atTop := by
  apply tendsto_atTop.mpr; intro m
  have he (t : ℝ) : ∀ᶠ μ : ℝ in atTop, t < Real.log μ := Real.tendsto_log_atTop.eventually (eventually_gt_atTop t)
  filter_upwards [(eventually_all_finset (Finset.range m)).mpr fun i _=> he (s i)] with μ h
  by_contra hm; have hf := chosen C μ
  exact (not_lt.mpr hf) (h _ (by simpa using (not_le.mp hm)))

lemma close_mesh : Tendsto (fun μ=> s (choose C μ)/Real.log μ) atTop (𝓝 1) := by
  have he : Tendsto (fun m=> s (m+1)/s m) atTop (𝓝 1) := by
    have hz := C.path.levels.fits.mesh.const_add 1
    rw [add_zero] at hz
    refine hz.congr' ?_
    filter_upwards [C.S.divergent.eventually (eventually_gt_atTop 0)] with m hm
    rw [C.S.scale_succ]
    change 1 + _/_=_
    field_simp
  apply Metric.tendsto_nhds.mpr; intro ε hε
  obtain ⟨N,h⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp he) ε hε)
  filter_upwards [(choosing C).eventually (eventually_ge_atTop (N+2)),Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with μ hm hμ
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero (show choose C μ ≠ 0 from by omega)
  have hj : s i < Real.log μ := by
    refine lt_of_not_ge (fun hz=> ?_)
    have hv := show choose C μ ≤ i from Nat.find_min' _ hz
    omega
  rw [hi]
  have hk := h i (by omega)
  rw [Real.dist_eq] at hk ⊢
  have hs := hi ▸ chosen C μ
  -- may need eventual positivity of s i. scale 0=0; i small. enlarge pre-tail instead.
  have HH : 0 < s i := by
    apply Real.log_pos
    exact (one_lt_inv₀ (C.S.a_pos i)).mpr ((C.S.strictAnti (show 0 < i from by omega)).trans_eq C.S.a_zero)
  have hx := (abs_lt.mp hk).2
  rw [abs_lt]
  constructor
  · have hz := (le_div_iff₀ hμ).mpr (by simpa only [one_mul] using hs : 1 * Real.log μ ≤ _); linarith
  have hm : s (i+1) < (ε+1)*s i := (div_lt_iff₀ HH).mp (by linarith only [hx])
  have hy : s i.succ < (ε+1)*Real.log μ := hm.trans (mul_lt_mul_of_pos_left hj (by linarith only [hε]))
  linarith only [(div_lt_iff₀ hμ).mpr hy]

/-- Read one positive actual-history coupling from a simultaneous ordered limit.
Not the prescribed X-space diagnostic. -/
def gLedger (C : Family G) (B : ℕ→ℝ) (μ : ℝ) : ℝ := (Real.sqrt (B (choose C μ)))⁻¹

include h hB hG
lemma band (m : ℕ) : B m ∈ Icc ((clock C).hatBeta m/2) (2*(clock C).hatBeta m) := by
  apply isClosed_Icc.mem_of_tendsto (hB m)
  apply (show ∀ᶠ i : ℕ×ℕ in f.fuse,m ≤ i.1 by
    rw [Order.fused,Order.late]; exact Eventually.of_forall fun k=>f.mesh.cofinal.eventually (eventually_ge_atTop m)).mono
  exact fun i hi=>(h.wilson.represents i.1 i.2 m hi).band

lemma ledger_positive (μ : ℝ) : 0 < gLedger C B μ := by
  unfold gLedger
  apply inv_pos.mpr; apply Real.sqrt_pos.mpr
  have ht : 1 < (clock C).hatBeta _ := C.path.levels.fits.delayed (choose C μ)
  linarith only [(band f C h hG hB (choose C μ)).1, ht]

lemma ratio : Tendsto (fun μ=>gLedger C B μ * (2*b₀*Real.log μ)^(1/2:ℝ)) atTop (𝓝 1) := by
  have hp := G.slopeConstant_pos hG
  rw [slope] at hp
  have hh := ((discrete f C h hB).comp (choosing C)).mul (close_mesh C)
  rw [mul_one] at hh
  have he := (tendsto_const_nhds (x:=2*b₀)).div hh hp.ne'
  rw [div_self hp.ne'] at he
  have hx : Tendsto (fun μ => 2*b₀*Real.log μ / B (choose C μ)) atTop (𝓝 1) := by
    apply he.congr'; filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0),
      (C.S.divergent.comp (choosing C)).eventually (eventually_gt_atTop 0)] with μ hμ ht
    change _/(B _/s _*(s _ / Real.log μ)) = _
    change 0 < s (choose C μ) at ht
    field_simp
  have hH := Real.continuous_sqrt.continuousAt.tendsto.comp hx
  rw [Real.sqrt_one] at hH
  apply hH.congr'; filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with μ hμ
  change (√_)=_
  rw [Real.sqrt_div (by positivity)]
  unfold gLedger; rw [div_eq_mul_inv,mul_comm]; simp [Real.sqrt_eq_rpow]

lemma vanishes : Tendsto (gLedger C B) atTop (𝓝 0) := by
  apply Tendsto.congr' (f₁:=fun μ=>gLedger C B μ * (2*b₀*Real.log μ)^(1/2:ℝ) / (2*b₀*Real.log μ)^(1/2:ℝ)) _
    ((ratio f C h hG hB).div_atTop ((tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.const_mul_atTop (slope ▸ Gauge.slopeConstant_pos hG))))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with μ hμ
  exact mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (by rw [← slope]; positivity [Gauge.slopeConstant_pos hG]) _).ne'
end Running
end YM.PertExtension
