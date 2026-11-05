import YM.Next.FLUCTUATIONS.Covariance
import YM.Next.FLUCTUATIONS.Global
import YM.Next.FLUCTUATIONS.Locality



/-!
# Analytic bound on the two cut defects in a halo

No information needed away from the cone of the tested row. Row
estimates pointwise for both Bool coordinates. w arbitrary, allowed to
be the actual thinned data even if converting links outside changes that
read. Only *separate* estimate on w needed then. Post-L pricing only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge}

lemma interior_cost (P : Teller G) (D : Patch) (hb : D.Branches P.bind G) :
    ∃ C τ r : ℝ, 0<C ∧ 0<τ ∧ 0<r ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
    ∀ (k : S.Choices) (R d : ℕ), 3*R+4+predReach S.patch ≤ d → ∀ (U : Config G f) (V : Config G c)
      (h : ℝ), 0 ≤ h → h ≤ r → ∀ (i : Twin c) (z : Site c → G.El),
    (∀ e : Bond f, separation i.1.1 (S.ratio.parent e.1) ≤ d →
      G.chord (gauge (z∘S.ratio.parent) U e) ≤ h) →
    (∀ e : Bond c, separation i.1.1 e.1 ≤ d → G.chord (gauge z V e) ≤ h) →
    ‖lGap T R U (S.prediction U k) V i‖ ≤ C * h * widen R h τ ∧
      ∀ (w : Twin c → G.Color) (q : ℝ), 0≤q → (∀ j, ‖w j‖ ≤ q) →
        ‖dGap T R V w i‖ ≤ C*q*widen R h τ := by
  obtain ⟨A,s,hA,hs,ha⟩ := extend_interior G
  obtain ⟨C,τ,r,hC,hτ,hr,hb⟩ := global_chart_cost P D hb
  let X := max 1 A
  have he : 1 ≤ X := le_max_left ..
  have hx : 0<X := zero_lt_one.trans_le he
  refine ⟨C*X^2,τ,min s (r/X),by positivity,hτ,lt_min hs (div_pos hr hx),?_⟩
  intro c f S T hD hP k R d hd U V h hh ht i z hf hg
  let U' := gauge (z∘S.ratio.parent) U
  let V' := gauge z V
  obtain ⟨a,h1,hU⟩ := ha S.ratio.parent i.1.1 d U' h hh (ht.trans (min_le_left ..)) hf
  obtain ⟨b,h2,hV⟩ := ha id i.1.1 d V' h hh (ht.trans (min_le_left ..)) hg
  have hi : A*h ≤ X*h := mul_le_mul_of_nonneg_right (le_max_right ..) hh
  have hm : X*h ≤ r := by rw [mul_comm]; exact (le_div_iff₀ hx).mp (ht.trans (min_le_right ..))
  have hg := gauge_gaps P T hP R U V k z i
  have hl := local_gaps T (hP.knobs.symm ▸ hP.kernel) R d i k U' (represent a) V' (represent b) hU hV hd
  obtain ⟨h3,h4⟩ := hb c f S T hD hP k R a b (X*h) (h1.trans hi) (h2.trans hi) hm i
  have hw : widen R (X*h) τ ≤ X * widen R h τ := by
    unfold widen
    have hv := le_mul_of_one_le_left (Real.exp_pos (-τ*R)).le he
    linarith
  constructor
  · rw [← G.norm_adjoint (z i.1.1), ← hg.1, hl.1]
    exact h3.trans ((mul_le_mul_of_nonneg_left hw (show 0 ≤ C*(X*h) by positivity)).trans_eq (by ring))
  intro w q hq hs
  let w' := turnData z (fun i : Twin c => i.1.1) w
  rw [← G.norm_adjoint (z i.1.1), ← hg.2 w, hl.2 w']
  apply (h4 w' q hq fun j => by unfold w' turnData; rw [G.norm_adjoint]; exact hs j).trans
  apply (mul_le_mul_of_nonneg_left hw (show 0 ≤ C*q by positivity)).trans
  rw [show C*q*(X*widen R h τ)=C*X*q*widen R h τ by ring]
  apply mul_le_mul_of_nonneg_right _ (widen_nonneg R hh)
  gcongr; nlinarith
end YM.Next.Fluctuations
