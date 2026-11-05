import YM.TraceExtension.Terrace.Delta
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "U#"=> C.labels.level 5
local notation "A"=> C.path.levels
variable {Z:Arch C} (hZ:steep 𝓛 Z) {S:Table C.book}{X:Scaling S} {i d j:ℕ}
variable (H:C.Makes) (hb:(𝓛:Filter (ℕ×ℕ)) ≤ F.fuse)
local notation "T!"=>C.labels.level d
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
variable {V:∀ i,Vane C i}{Y:∀ (d i:ℕ),(Cells.standard C).Field d→L[ℂ] C.label d}{a:(Cells.standard C).Hierarchy}
variable (hq:Gondola F a X 𝓛 V Y)
variable {s:ℕ → Bowl (C.labels.level 5) →L[ℝ] (TableOne a.spin)}
variable (K:Sceptre C W)(θ:PostT C.path.levels)(hG:G.Simple) (hp: Spun Z X V a s)
def Lease(F:Frame G 5) (h:G.Simple): Bowl F →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((rho h).comp (plate F).toLinearMap)
def hueK (Y:Levels G) (i:ℕ):= AgeK Y (1/5) i
lemma Lease_alive (F':Frame G 5) (hG:G.Simple): Lease F' hG (Stem5 F')=0:=by
   change rho hG ((plate F') (Stem5 F')) = _; rw[Stem5,LinearEquiv.apply_symm_apply]; exact rho_eom hG _ (fun i=> eom_null i)
-- The abstract sensor frontier. Polling at measure comparisons and H rank pins required.
structure Prosper (V:∀ i,Vane C i)(h:G.Simple)(a:(Cells.standard C).Hierarchy)(s:ℕ→Bowl (C.labels.level 5) →L[ℝ] (TableOne a.spin)) : Prop where
   alpha : Tendsto s atTop (𝓝 (Vbase a.spin).toContinuousLinearMap)
   vote : ∃ μ:ℕ→TableOne a.spin→ₗ[ℝ] ℝ, ∃ c:ℝ,0≤c∧ (∀ᶠ i in atTop,∀ y,‖μ i y‖ ≤ c*‖y‖) ∧
        (∀ e:ℝ,0<e → ∀ᶠ i in atTop,∀ y, ‖hueK (A) (Stern V i)*(μ i (s i y) - Lease U# h y)‖ ≤ e * ‖y‖)

include hp hZ H hb hr hq K θ hG
set_option maxHeartbeats 800000 in
lemma springs (v:ℕ→ Bowl (C.labels.level 5)) (hv:Tendsto v atTop (𝓝 (Stem5 (U#))))
    (hk:Tendsto (fun i=> hueK A (Stern V i) • s i (v i)) atTop (𝓝 0))(hw: Tendsto (fun i=> hueK A (Stern V i)*Lease U# hG (v i)) atTop (𝓝 0)) : Prosper V hG a s:=by
    let x(i):= hueK (A) (Stern V i); have hP(i:ℕ): 0<x i:=wake ..; have hC:Tendsto x atTop atTop:= ((Zn.awe (by norm_num : 0 < (1/5:ℝ))).comp (hrate _ hG)|>.comp ( (Sstar (A)).comp hq.growth))
    have hx : Tendsto (fun i=> s i (v i)) atTop (𝓝 0):=by
        have he := (tendsto_inv_atTop_zero.comp hC).smul hk; rw[zero_smul] at he; exact he.congr (fun i=> inv_smul_smul₀ (hP i).ne' _)
    obtain ⟨U,t,hU,hT,hK⟩:= lensP hZ H hb hr hq K θ hG hp
    let B':= LinearMap.toContinuousLinearMap U; let f:=LinearMap.toContinuousLinearMap (Vbase a.spin); let t'(i):=LinearMap.toContinuousLinearMap (t i)
    have ht:Tendsto t' atTop (𝓝 B'):=by refine fitV (E:=↥(TableOne a.spin)) (H:=↥(Bowl (U#))) t' B' ?_; exact hT
    have hr: f.comp B'=ContinuousLinearMap.id ℝ _:= ContinuousLinearMap.ext hU
    have hR:∀ᶠ i in atTop, (s i).comp (t' i)=ContinuousLinearMap.id ℝ _:= hK.mono fun i hi=>ContinuousLinearMap.ext hi
    let F':= (U#); let F₀:= Stem5 (U#); let ξ:= Lease (U#) hG
    have hh:= scout (H:=↥(TableOne a.spin)) (E:=↥(Bowl (U#))) f s B' t' F₀ v ht hr hR hv hx (Stem5_alive _ hG) (fun y=> Stem5_kernel (a:=a.spin) y hG)
    obtain ⟨m,M,h₁,h₂⟩:= expenses (H:=↥(TableOne a.spin)) (E:=↥(Bowl (U#))) f s B' t' F₀ v x ξ ht hR hv hh (Stem5_alive _ hG) (fun p=> Stem5_kernel (a:=a.spin) p hG) hr (by exact hk) (by exact hw)
    refine ⟨hh,m,M,h₁,h₂.1,?_⟩; change ∀ e:ℝ,0<e → ∀ᶠ i in atTop,∀ y, ‖x i*(m i (s i y) - ξ y)‖ ≤ _; exact h₂.2
end YM.Trace.Terrace
#print axioms YM.Trace.Terrace.springs
