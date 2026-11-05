import YM.WilsonBulk.Build.Rains

/-!
# Signed shuffle centered orientations

Keep step size crossing and independent free periods. No curve lift here.
Input permutation of physical tags in opacity steps will remain explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Lattice Laurent RG Precision Exterior FreeResolvent Sheet
open Function Filter Wilson Finset
open Stationary (Army)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {κ : Type} [Fintype κ] {G : Gauge} {c f n : Side} {S : StepData c f}
variable (s : Signed) (b : Site n)

-- map signed tangent at pulled orientation. exactly linear, no approximation after log

def tone (s : Signed) (e : Edge (Site n)) : ℝ := if s.flip e.2 then -1 else 1
def swivel (s : Signed) (b : Site n) (x : Interface G n) (j : Pennant G n) :=
  let e : Edge (Site n) := (j.1,axisEquiv.symm j.2.1); let u:= Wilson.sendEdge s b e; tone s e * x (u.1,coord u.2,j.2.2)
lemma swivel_at (x : Interface G n) (e : Edge (Site n)) :
   traces G n 1 (swivel s b x) (e.1,coord e.2)= tone s e • traces G n 1 x ((Wilson.sendEdge s b e).1, coord ((Wilson.sendEdge s b e).2)) := by
    ext i; simp only [traces_at]; unfold swivel ix; simp only [show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _, Prod.mk.eta]; rfl
lemma swivel_birth : swivel s b (0:Interface G n)=0 := by ext i; simp [swivel]
lemma swivel_jet : ContDiff ℝ ω (swivel (G:=G) s b) := by apply contDiff_pi.mpr; intro i; unfold swivel; exact contDiff_const.mul (contDiff_apply ℝ ℝ _) -- inspect
lemma swivel_sign (x : Interface G n) : signal G n (swivel s b x)= pull s b (signal G n x) := by
  ext1 i; rw [signal_at,swivel_at]; unfold tone pull Wilson.sendEdge Step.read; cases h : s.flip i.2 <;> simp [posDir,Step.rotate,h,signal_at,Work.F03.exp_neg_color]
lemma swivel_id : swivel (G:=G) 1 (0:Site n)=id := by
  ext1 x; ext1 i; rcases i with ⟨i,j,d⟩; obtain ⟨j,rfl⟩:= axisEquiv.surjective j; simp [swivel,Wilson.sendEdge, Step.rotate_one,Step.used,affine,tone,posDir]; rw [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _] -- fix

def Spins (φ ψ : Logbook G n) := submit (exposure (swivel s b)) ψ = φ
lemma Spins.pair {φ ψ : Logbook G n} {v : Tabletop κ → Interface G n} (h : Spins s b φ ψ) (he : ContDiffAt ℝ ω v 0) (hp : v 0=0) : submit (exposure (swivel s b ∘ v)) ψ= submit (exposure v) φ := by rw [← exposure_encode he (swivel_jet ..|>.contDiffAt) hp (swivel_birth ..),h]
lemma spins_id (φ : Logbook G n) : Spins 1 0 φ φ := by unfold Spins; rw [swivel_id,exposure_id,submit_id]
lemma army_spin {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E→ Config G n} (h : Army U 0) : Army (pull s b ∘ U) 0 := by
  intro i; simp only [Function.comp_apply,pull]; unfold Step.read; split; exact h.inv _; exact h _

variable {s} {b} in
lemma rhythm {κ : Type} [Fintype κ] (s : Signed) (b : Site n) {v w : Tabletop κ→Interface G n} {t : Tabletop κ → Site n → G.El} (h : Army t 0) {k : G.El} (he : t 0=Function.const (Site n) k)
    (hv : ContDiffAt ℝ ω v 0) (hw : ContDiffAt ℝ ω w 0) (hx : v 0=0) (hy : w 0=0) {φ ψ : Logbook G n} (hp : Dances ψ) (hz : Spins s b φ ψ) (hm : ∀ᶠ z in 𝓝 0,signal G n (w z)= Lattice.gauge (t z) (pull s b (signal G n (v z)))) : submit (exposure w) ψ=submit (exposure v) φ := by
  rw [← hz.pair s b hv hx, hp.visitor h he ((swivel_jet s b).contDiffAt.comp _ hv) hw (show (swivel s b ∘ v) 0=0 by rw [Function.comp_apply,hx,swivel_birth]) hy (hm.mono (by intro x hx; rw [Function.comp_apply,swivel_sign]; exact hx))]
end YM.WilsonBulk.Atelier
