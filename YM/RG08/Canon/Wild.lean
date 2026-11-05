import YM.RG08.Canon.Taste
/-! # Return from centered Hessian coordinates, include shifted Haar
and off-period discrepancy until bulk comparison of coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {σ K Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
variable {η:ℝ} (v:Stationary.Link G c) {t:S.Choices} {D : ChartRatio G} {L : fieldDir G c 1 → (AxisChart G F)≃L[ℝ] AxisChart G F}
local notation "U" => AxisChart G F
local notation "Y" => F.Slice G
variable {V:ℕ→Config G f→ℝ} (h : Salvo t F R p ρ η L)
variable {Q : Pot G 2} {W : Air G} (hp : ∀ i,Caper Q W 2 i (V i)) (hr : Cask p R f Q W)

def mixL (s:ℝ) (F:Forest S.ratio) : F.Slice G := fun i=> replica S.ratio (input G c (s•v)) i
include h hr
lemma tram_flat (hx : S.patch.Branches S.kernel G): victory F t p R ρ 0=0 := by
  unfold victory; rw [map_zero,h.critical.1]; unfold tested; simp only [Precision.link_one,lifted,replica_one]; rw [(cask_open p R hr).1]; unfold noiseTaylor; simp [Push.settled S hx]

abbrev timeP (_h:Salvo t F R p ρ η L) (x:ℝ):= victory F t p R ρ (x•v)
abbrev weighting (D:ChartRatio G) (y:ℝ):= -(1:ℝ)+timeP v h y/y^2+scent v D h y
-- weighting as above actually h arguments check
lemma known (hd : LocalRatio D) (hw : R.Bounds p σ K Λ) (hs : G.Simple) (hx:S.patch.Branches S.kernel G) : Bill 0 (weighting v h D) := by
  have H := (campaign h.critical hx hw t h.ears h.price zero_lt_one hd).1
  let A:=victory F t p R ρ
  let C:=timeP v h
  have hp x : jet A 1 x=0 := by unfold jet; rw [iteratedFDeriv_one_apply,first_invariant hs H]; simp
  have ht : Fit 2 C 0 := by
    let b n:=jet A n v
    have hy : peval b 1=(0:ℝ→ℝ):=by funext x; unfold peval PertExtension.Series.Zone.eval; simp only [sum_range_succ,sum_range_zero,zero_add, pow_zero,one_smul,b,hp,jet_zero]; rw [show A 0=0 from tram_flat h hr hx]; simp
    rw [← hy]; exact directions H.analytic.contDiffAt v 1
  have hg : Bill 0 (fun t:ℝ=> C t/t^2) := (show Fit 0 (fun t:ℝ=> C t/t^2) (fun t:ℝ=>0/t^2) from ht.shorten (n:=0) (k:=2)).havePay (by simpa using bill_const (0:ℝ)) (by decide)
  have hi := spanL_e v
  have hu := (born hw h.critical h.ears h.price hd t).continuousAt.tendsto.comp hi
  exact bill_add (bill_add (bill_const (-(1:ℝ))) hg) (life_price ((hu.sub (tendsto_const_nhds (x:=thermal F t p R ρ D 0))).mono_left nhdsWithin_le_nhds))
-- no V expectation modulation before winding control.
local notation "Π" => sublet v D h
local notation "Θ" => lance v h
local notation "J" => morsel v h V
local notation "Ω" => discPay S G F (fun _=>v) t 2 V
local notation "Φ" => Real.exp ∘ weighting v h D
private abbrev offset (s : ℝ)(x : Y) := Ω s (x*mixL v s F)

include hp
lemma centered_once (hd : LocalRatio D) (hw : R.Bounds p σ K Λ) (hx:S.patch.Branches S.kernel G) :
    let m:ℕ→ℝ:= moment (hold G F.Free) Π J
    ∃ s ∈ 𝓝 (1:Y), ∀ A : ℝ → Set (Y), (∀ᶠ t' in 𝓝[>] 0, MeasurableSet (A t') ∧ A t'⊆s) →
      (∃ y ∈ 𝓝 1,∀ᶠ t' in 𝓝[>] 0,y⊆A t') →
      Fit 3 (fun t'=> (Φ) t'*((t'^Module.finrank ℝ (U))⁻¹*(∫ x in A t', Ω t' (x*mixL v t' F) ∂F.order G))) (peval m 2) := by
  intro m
  let B k:=offset v (V:=V) (t:=t) (F:=F) k
  have hP (s:ℝ): Measurable (discPay S G F (fun _=>v) t 2 V s) := Real.continuous_exp.measurable.comp ((labs_meas S (fun i=> (hp i).stamp) t hx _ (w:=fun _=> input G c (s•v)) measurable_const (F.continuous_drape.measurable) measurable_const 2).neg.div_const _)
  have hB (s) : Measurable (B s) := (hP s).comp (show Measurable (fun x:Y=> x*mixL v s F) from measurable_id.mul measurable_const)
  let a:=ρ ∘ spanL v; let M s:=L (spanL v s)
  let u:ℝ→ℝ:= timeP v h
  have ha : a 0=0 := by simp [a,spanL,h.critical.1]
  have he : ContDiffAt ℝ ω (spanL v) 0:=spanL_changes v|>.contDiffAt
  have hf : spanL v 0=0 := by simp [spanL]
  refine stadium_rules G F.Free M a B Π J (Φ) hd 2 (gleam_start v h hw hd) (mundane v h hp hr) (expulse v h hp hr).1 (expulse v h hp hr).2 (Eventually.of_forall hB) ?_ ?_ ((hf.symm ▸ h.critical.2.1: ContDiffAt ℝ ω _ (spanL v 0)).comp _ he).continuousAt ha ⟨Set.univ,Filter.univ_mem,?_⟩
  · have hh : ContDiffAt ℝ ω (fun s=>(M s).toContinuousLinearMap) 0:= (show ContDiffAt ℝ ω (fun i=>(L i).toContinuousLinearMap) (spanL v 0) from by rw [hf]; exact h.smooth).comp _ he
    exact ((hh.comp (f:=Prod.snd) (0 : U × ℝ) contDiffAt_snd).clm_apply contDiffAt_fst).continuousAt
  · have hh : ContDiffAt ℝ ω (fun s=>(M s).symm.toContinuousLinearMap) 0:= (show ContDiffAt ℝ ω (fun i=>(L i).symm.toContinuousLinearMap) (spanL v 0) from by rw [hf]; exact h.reverseL).comp _ he
    exact ((hh.comp (f:=Prod.snd) (0 : U × ℝ) contDiffAt_snd).clm_apply contDiffAt_fst).continuousAt
  filter_upwards [(spanL_e v|>.eventually h.honor).filter_mono nhdsWithin_le_nhds,eventually_pos] with s he hn
  intro x _
  rw [projection_eq,abs_of_pos (show 0<swing (M s) from he.1)]
  let r:= s•plates G F.Free x
  have hh : r.2=s:=mul_one _
  have hI : incount v ρ L r=s • M s x + a s := by unfold incount; rw [hh]; change a s+M s (s • x)=_; rw [map_smul,add_comm]
  let E := laboratory S t 2 V s (input G c (s•v)) (Θ r)
  have hU : colorX v r=spanL v s:= congr_arg _ hh
  rw [show (J) r= E-u s + s^2 by unfold morsel E; rw [hU,hh]; rfl]
  change (Π) r * Real.exp _ = Real.exp (weighting v h D s)*(swing _ *(jacobian D _*B s _))
  have hk : B s (expLinks G _ (s•M s x+a s))=Real.exp (-E/s^2):= by
    rw [← hI]; unfold B offset discPay E lance; rw [hU]; rfl
  rw [sublet,hU,hh,hI,hk]
  unfold weighting
  change Real.exp (scent v D h s)*swing (M s)*jacobian D _*Real.exp (-_/s^2)= Real.exp (_+u s/s^2+_) * _
  rw [show Real.exp (-(E-u s+s^2)/s^2)=Real.exp (-(1:ℝ)+u s/s^2)*Real.exp (-E/s^2) by rw [← Real.exp_add]; congr 1; field_simp; ring, Real.exp_add (-(1:ℝ)+u s/s^2) (scent v D h s)]
  ring
end YM.RG08.Canon
