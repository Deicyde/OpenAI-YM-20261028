import YM.AnalyticNext.QUARTIC_MATCH.Local.Liable

/-!
# The profiles to be periodized. Width and cost before L

All vectors per sparse basis slot. Thus supplies the entry estimates for
both potential resolutions, including post-cubic subtraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain Premium Evoke Budget
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Rotate
variable {G : Gauge} {W : PathData G} {S : Side} {σ C D R η : ℝ}
lemma led_lower (h : Led W S 4 η σ D C R) (hp : 0 ≤ η) : Led W S 3 η σ D C 0 := by
  refine ⟨h.down,(show 5*↑(3:ℕ)*η≤_ from by push_cast at *; linarith [show 5*(4:ℝ)*η≤σ*S.val from by exact_mod_cast h.repute]), h.curves,?_,Access.quiet (by omega) le_rfl⟩
  cases h.three with
  | clears hσ hq hk => exact Access.clears hσ (by push_cast at *; linarith) hk
  | missing hx ht => exact Access.missing hx ht
  | quiet hi hh => omega
end Rotate

namespace Wages
variable (G : Gauge) (j : ℕ) {D u κ η C a : ℝ} (hp : 0<u) (he : boom u ≤ η) (hκ : 0<κ)
open Green (wt)
open Tracks
include hp he hκ

abbrev Tester (G : Gauge) (c : Side) := Cell (Per c) × G.Color
def fromT {c : Side} (i : Tester G c) : Dir G c := sparse i.1 i.2

theorem exchanged (D : ℝ) (ha : 0<a) (hh : u ≤ Tracks.purchase j a η C κ) :
    ∃ R : ℝ, 0≤R ∧ ∀ (c f : Side) (S : StepData c f) (p : Clip) (W : PathData G) (θ : S.Choices) (σ τ K Λ R3 : ℝ),
      S.patch.J=j → S.kernel.penalty=κ → S.patch.Branches S.kernel G → W.Bounds p τ K Λ → Rotate.Led W S.patch.L 3 (boom u) σ D R3 0 →
        ∀ (U : Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (H : Bed), Evoke.motion S U η C → H.metric.strip η C →
          Attached H W → Sworn H f G → Floor H p f a C → ∀ X : Dir G c → Vertical G c f, X 0=0 → OnShell (cash S θ p W) X 0 →
          fderiv ℝ X 0=stance (installed S.ratio U) → (∀ u w,cop S (D2 X 0 u w)=0) →
            ∀ (x y b d : Tester G c), let T (i : Tester G c) := fromT G i; let L (i : Tester G c) := tangent X 0 (fromT G i)
            wt (rate u) x.1.1 y.1.1 * (wt (rate u) x.1.1 b.1.1 * wt (rate u) x.1.1 d.1.1) *
             |leg (cash S θ p W) 0 (L b) (L d) (D2 X 0 (T x) (T y))| ≤ R*assistance S.patch.L R3 0^2 * ‖x.2‖ * ‖y.2‖ * ‖b.2‖* ‖d.2‖ := by
  obtain ⟨r,hr,H⟩ := Wages.bending (C:=C) G j 3 le_rfl hp he hκ D
  let δ := Hessian.reserve j a κ/2
  have hd : 0 < δ := half_pos (reserve_pos _ _ _ ha hκ)
  refine ⟨r*r/δ,by positivity,?_⟩
  intro c f S p W θ σ τ K Λ R3 h1 h2 h3 h4 h5 U M hy hα hA hS hF X hX hs hU hCop x y b d T L
  let e := S.ratio
  let A := cash S θ p W; let t := assistance S.patch.L R3 0; let w i j := wt (rate u) i j (f:=c)
  let J (x : Tester G c) := x.1.1
  let z := e.embed (J x)
  let q := D2 X 0 (T x) (T y); let Y := polar S u z q
  let V := w (J x) (J y); let F := w (J x) (J b)*w (J x) (J d)
  let B := r*t*‖x.2‖* ‖y.2‖; let E := r*t*‖b.2‖* ‖d.2‖
  have ht : 0≤t := zero_le_one.trans (cost_support h5); have hB : 0≤B := by unfold B; positivity
  have hE : 0≤E := by unfold E; positivity
  have hV : 0 < V := Green.wt_pos ..; have hK : 0 < F := mul_pos (Green.wt_pos ..) (Green.wt_pos ..)
  have he1 (ξ : Tester G c) : tangent X 0 (fromT G ξ) = external (installed S.ratio U) ξ.1 ξ.2 := by unfold tangent; rw [hU]; rfl
  have hm := H _ _ S p W θ σ τ K Λ R3 0 h1 h2 h3 h4 h5 U hy
  have he' : |u| ≤ boom u := by rw [abs_of_pos hp]; unfold boom; linarith
  have hW : ∀ W, |leg A 0 (L x) (L y) (polar S u z W)| ≤ (B/V)*shares S W := by
    intro W
    have hp' (i : Site f) := embedded e.count hp z (e.embed (J y)) i
    have H' := hm x.1 y.1 x.2 y.2 (J x) (J x) u V W he' hV.le (fun i => by
      have hv : V=wt (rate u/e.count.val) z (e.embed (J y)) := (accrual S ..).symm
      rw [hv]; exact hp' i)
    rw [div_mul_eq_mul_div]; apply (le_div_iff₀ hV).mpr; unfold L; rw [he1,he1,mul_comm]; exact H'
  have Hℓ : shares S Y ≤ (B/V)/δ := by
    apply (le_div_iff₀ hd).mpr; rw [mul_comm]
    have hi : |u| ≤ Tracks.purchase S.patch.J a η C S.kernel.penalty := by rw [h1,h2,abs_of_pos hp]; exact hh
    have hx := flight S ha hF h4 hA hS θ h3 hX hs (T x) (T y) (lt_of_lt_of_le (booms hp) he) hi hα (div_nonneg hB hV.le) (hCop ..) z hW
    rw [h1,h2] at hx; exact hx
  have h' : F* |leg A 0 (L b) (L d) q| ≤ E*shares S Y := by
    have hx := hm b.1 d.1 b.2 d.2 (J x) (J b) (-u) F Y (show _ from by rwa [abs_neg]) hK.le (fun i => by
      have hp := severs e.count hp z (e.embed (J b)) (e.embed (J d)) i
      have hv : F=wt (rate u / e.count.val) z (e.embed (J b)) * wt (rate u / e.count.val) z (e.embed (J d)) :=
        (congr_arg₂ HMul.hMul (accrual S (J b) (J x) _) (accrual S (J d) (J x) _)).symm
      rw [hv,neg_neg]; exact hp)
    unfold L; rw [he1,he1];
    rw [show polar S (-u) (S.ratio.embed (J x)) Y=q from cancels ..] at hx; exact hx
  change V*F* _ ≤ _
  rw [mul_assoc V]; apply ((mul_le_mul_of_nonneg_left (h'.trans (mul_le_mul_of_nonneg_left Hℓ hE)) hV.le)).trans_eq
  change V* (E * (B/V/δ))=r*r/δ*t^2*‖x.2‖*‖y.2‖*‖b.2‖*‖d.2‖; unfold B E; field_simp
end Wages
end YM.AnalyticNext.QuarticMatch.Local
