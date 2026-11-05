import YM.WilsonBulk.Build.Parchment
import YM.Work.F03.Flat

/-!
# Ward predicates on free tapes (before and after tuning)

Full rescaled (\*not\* only infinitesimal) gauge: true at every formal power
across node parameters based at any common constant color. Proofs use real
analytic local coordinates. `Spins` signed and shift general.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Lattice Laurent RG Precision Exterior FreeResolvent Sheet
open Function Filter Wilson
open Stationary (Army)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {κ ξ : Type} [Fintype κ] [Fintype ξ] {G : Gauge} {c f n : Side} {S : StepData c f}
abbrev Needle (G : Gauge) (n : Side) := FreeResolvent.Slot G n 0
abbrev GTable (G : Gauge) (n : Side) := Tabletop (Chamber (Pennant G n) (Needle G n))
def curtainK (n : Side) (k : G.El) (x : Tabletop (Needle G n)) : Site n→ G.El := fun y=> k * G.lieExp (-traces G n 0 x (y,vac))
def cloakK (n : Side) (U : Config G n) : Interface G n:= (traces G n 1).symm (fun i=>G.plog (G.mat (U (i.1,axisEquiv.symm i.2))))
lemma curtainK_zero (n : Side) (k : G.El) : curtainK n k 0= Function.const _ k := by ext1 i; simp [curtainK]
lemma cloakK_birth : cloakK n (1:Config G n)=0 := by unfold cloakK; simp only [Pi.one_apply]; rw [show (fun _:Body 1 n=> G.plog (G.mat 1))=0 from funext fun i=> by simp,map_zero] -- inspect
lemma cloakK_real : ∀ᶠ U in 𝓝 (1:Config G n), signal G n (cloakK n U)=U := by
  have he e:= ((continuous_apply (A:=fun _:Edge (Site n)=> G.El) e).tendsto (1:Config G n)).eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with U h; ext1 i; rw [signal_at,cloakK,ContinuousLinearEquiv.apply_symm_apply, show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; exact h i
lemma cloakK_tip : ∀ᶠ x in 𝓝 (0:Interface G n), cloakK n (signal G n x)=x := by
  have ht i := ((continuous_apply i).comp (traces G n 1).continuous).tendsto 0
  simp only [Function.comp_apply,map_zero,Pi.zero_apply] at ht
  filter_upwards [eventually_all.mpr (fun i=>(ht i).eventually G.plog_left)] with x hx
  apply (traces G n 1).injective
  rw [cloakK,ContinuousLinearEquiv.apply_symm_apply]; ext1 ⟨e,i⟩; obtain ⟨j,rfl⟩:= axisEquiv.surjective i
  rw [axisEquiv.symm_apply_apply,signal_at]; exact hx _
lemma cloakK_pill {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → Config G n} (h : Army U 0) (he : U 0=1) : ContDiffAt ℝ ω (cloakK n ∘ U) 0 := by
  apply (traces G n 1).symm.contDiff.contDiffAt.comp (f:=fun z i=> G.plog (G.mat (U z (i.1,axisEquiv.symm i.2)))) (0:E); refine contDiffAt_pi.mpr fun i=> ContDiffAt.comp (g:=G.plog) _ ?_ (h _)
  rw [he,Pi.one_apply,G.mat_one]; exact G.plog_diff

lemma signal_force {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E→ Interface G n} (hv : ContDiffAt ℝ ω v 0) : Army (signal G n ∘ v) 0 := by
  intro i; simp_rw [Function.comp_apply,signal_at]; exact G.exp_jet.contDiffAt.comp _ (contDiffAt_pi.mp ((traces G n 1).contDiff.contDiffAt.comp _ hv) _)
lemma weatherK {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : G.El) {x : E→Tabletop (Needle G n)} (h : ContDiffAt ℝ ω x 0) : Army (curtainK n k ∘ x) 0 := by
  intro y; simp only [Function.comp_apply,curtainK,G.mat_mul]; exact contDiffAt_const.mul (G.exp_jet.contDiffAt.comp (0:E) (contDiffAt_pi.mp ((traces G n 0).contDiff.contDiffAt.comp (0:E) h) _).neg)
lemma gauge_absolute {k : G.El} : Lattice.gauge (Function.const (Site n) k) (1:Config G n)=1 := by ext1 i; simp [Lattice.gauge]
def narrative (n : Side) (k : G.El) (z : GTable G n) := Lattice.gauge (curtainK n k (lower _ _ z)) (signal G n (upper _ _ z))
def pigment (n : Side) (k : G.El) : GTable G n → Interface G n:= cloakK n ∘ narrative n k
lemma narr_birth (n : Side) (k : G.El) : narrative n k 0=1 := by rw [narrative,map_zero,map_zero,curtainK_zero, signal_zero,gauge_absolute]
lemma pigment_birth (k : G.El) : pigment n k 0=0 := by rw [pigment,Function.comp_apply,narr_birth, cloakK_birth]
lemma narrative_jet (n : Side) (k : G.El) : Army (narrative n k) 0 := by
  let D:=lower (Pennant G n) (Needle G n); let A:=upper (Pennant G n) (Needle G n); exact (weatherK k D.contDiff.contDiffAt).slant (signal_force (v:=A) A.contDiff.contDiffAt)
lemma pigment_jet (k : G.El) : ContDiffAt ℝ ω (pigment n k) 0 := cloakK_pill (narrative_jet n k) (narr_birth n k)
lemma pigment_laid (k : G.El) : signal G n∘ pigment n k=ᶠ[𝓝 0] narrative n k :=
  ((narr_birth n k) ▸ ((narrative_jet n k).cont.tendsto) : Tendsto (narrative n k) (𝓝 0) (𝓝 1)).eventually cloakK_real

-- universal gauge predicate and test on any finite-dimensional real rescaled parameters

def Dances (φ : Logbook G n) := ∀ k:G.El,submit (exposure (pigment n k)) φ=mountain (Pennant G n) (Needle G n) φ
lemma preimage {κ A : Type} [Fintype A] [Fintype κ] {k : G.El} {t : Tabletop κ→ A → G.El} (h : Army t 0) (he : t 0=Function.const _ k) :
    let p:= fun x i=> G.plog (G.mat (k⁻¹*t x i))
    ContDiffAt ℝ ω p 0 ∧ p 0=0 ∧ (fun x i=> k * G.lieExp (p x i))=ᶠ[𝓝 0] t := by
  intro p
  let g:Tabletop κ→ A → G.El := fun x i=> k⁻¹*t x i
  have hh : Army g 0 := (Stationary.Army.park (Function.const A k⁻¹) _).mul h
  have hg : g 0=1 := funext fun i=> by simp [g,he]
  refine ⟨?_,?_,?_⟩
  · refine contDiffAt_pi.mpr fun i=> ContDiffAt.comp (g:=G.plog) _ ?_ (hh i); rw [show k⁻¹*t 0 i=g 0 i from rfl,hg,Pi.one_apply,G.mat_one]; exact G.plog_diff
  · ext1 i; change G.plog (G.mat (g 0 i))=_; simp [hg]
  have hi:= hh.cont.tendsto; rw [hg] at hi; filter_upwards [eventually_all.mpr fun i:A=> (tendsto_pi_nhds.mp hi i).eventually G.plog_right] with x hx; ext1 i; unfold p; rw [show k⁻¹*t x i=g x i from rfl, hx i, show g x i=k⁻¹*t x i from rfl, mul_inv_cancel_left]
lemma emitter {t : Tabletop κ→ Site n → G.El} (h : Army t 0) {k : G.El} (he : t 0=Function.const _ k) : ∃ g : Tabletop κ→Tabletop (Needle G n), ContDiffAt ℝ ω g 0 ∧ g 0=0 ∧ t=ᶠ[𝓝 0] curtainK n k ∘ g := by
  let p:= fun x i=> G.plog (G.mat (k⁻¹*t x i)); obtain ⟨hp,h₁,h₂⟩:= preimage h he
  let f (x:Tabletop κ) (j:Body 0 n): G.Color := -p x j.1
  have hv : ContDiffAt ℝ ω f 0:= contDiffAt_pi.mpr fun i=> (contDiffAt_pi.mp hp i.1).neg
  refine ⟨(traces G n 0).symm ∘ f,(traces G n 0).symm.contDiff.contDiffAt.comp (0:Tabletop κ) hv,?_,?_⟩
  · rw [Function.comp_apply,show f 0=0 from ?_,map_zero]; ext1 i; change -p 0 i.1=0; rw [show p 0 i.1=0 from congr_fun h₁ _, neg_zero]
  suffices curtainK n k ∘ ((traces G n 0).symm ∘ f)=(fun x i=> k* G.lieExp (p x i)) from this.symm ▸ h₂.symm
  ext1 x; ext1 i; simp [f,curtainK,Function.comp]
lemma Dances.visitor {v w : Tabletop κ→Interface G n} {t : Tabletop κ → Site n → G.El} (h : Army t 0) {k : G.El} (he : t 0=Function.const (Site n) k)
    (hv : ContDiffAt ℝ ω v 0) (hw : ContDiffAt ℝ ω w 0) (hx : v 0=0) (hy : w 0=0) {φ : Logbook G n} (hp : Dances φ) (hm : ∀ᶠ z in 𝓝 0,signal G n (w z)= Lattice.gauge (t z) (signal G n (v z))) : submit (exposure w) φ=submit (exposure v) φ := by
  obtain ⟨g,hg,h0,ht⟩:= emitter h he
  let U (x : Tabletop κ) : GTable G n:= Sum.elim (v x) (g x); let C:= pigment n k
  have hb : ContDiffAt ℝ ω U 0:= assemble_jet hv hg; have hu : U 0=0:= assemble_zero hx h0
  have hH : ∀ (i : Tabletop κ), upper _ _ (U i)=v i:=fun _=>rfl
  have hU : Tendsto U (𝓝 0) (𝓝 0):= hu ▸ hb.continuousAt.tendsto; have hW : Tendsto w (𝓝 0) (𝓝 0):=hy ▸ hw.continuousAt.tendsto
  have hc : C∘ U=ᶠ[𝓝 0] w := by
    filter_upwards [hm,hU.eventually (pigment_laid k),ht, hW.eventually (cloakK_tip)] with z hz hl ht hk
    dsimp only [C,pigment,Function.comp_apply,narrative]; rw [show curtainK n k (lower _ _ (U z))=t z from ht.symm, hH, ← hz]; exact hk
  let M:=upper (Pennant G n) (Needle G n)
  have hN:M∘ U=v:=funext hH
  have ha : submit (exposure M) φ= mountain (Pennant G n) (Needle G n) φ:= by unfold mountain M; rw [upper_code]
  rw [← expose_match hc,←exposure_encode hb (pigment_jet _) hu (pigment_birth _),show submit (exposure C) φ=_ from hp k,← ha, exposure_encode hb M.contDiff.contDiffAt hu (map_zero _),hN]
end YM.WilsonBulk.Atelier
