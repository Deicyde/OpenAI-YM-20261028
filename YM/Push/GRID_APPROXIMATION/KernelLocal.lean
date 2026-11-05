import YM.Push.GRID_APPROXIMATION.Cone
import YM.Push.GRID_APPROXIMATION.KernelBasic
import YM.Push.GRID_APPROXIMATION.Product



/-!
# The actual conditional pullback fits a finite cone, factors on disjoint cones

Summing unused tags with their actual masses. Site tags can be read in
neighboring bonds: in particular, not assuming that all coarse V bonds
are conditionally independent given the fine field. No conditioning on
large/small field events.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Set Filter MeasureTheory Function
open scoped Topology BigOperators

variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)

section parts

/-- Evaluate the actual conditional density of one link, integrating just
the bond tag, with required site tags still shared. -/
def noiseLink (Y v : G.El) := (S.penaltyZ β G)⁻¹ * S.penaltyWeight β (v * Y⁻¹)

def perLink (U : Config G f) (t : S.SitesChoice) (e : Edge (Site c)) (v : G.El) : ℝ :=
    ∑ r : S.patch.Points, S.patch.predictorMass S.kernel (S.connector U t e) r *
      noiseLink S β (S.patch.predict S.kernel (S.connector U t e) r) v

def perSite (U : Config G f) (x : Site c) (r : S.patch.FrameTag) : ℝ :=
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) r

/-- Identity including all tags (canonical minimize with uniform unused
tags, fallback eligible etc.), volume needn't be large. -/
lemma density_parts (U : Config G f) (V : Config G c) :
    S.density β U V = ∑ t : S.SitesChoice, (∏ x, perSite S U x (t x)) * ∏ e, perLink S β U t e (V e) := by
  classical
  unfold StepData.density; rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold StepData.likelihood StepData.noise perSite perLink noiseLink StepData.prediction
  rw [Fintype.prod_sum (fun e r => _)]; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma noiseLink_cont (Y : G.El) : Continuous (noiseLink S β Y) := by
  unfold noiseLink StepData.penaltyWeight; fun_prop
lemma noiseLink_mass (Y : G.El) : (∫ v, noiseLink S β Y v ∂G.probHaar) = 1 := by
  have h := (measurePreserving_mul_right G.probHaar Y⁻¹).integral_comp
    ((Homeomorph.mulRight Y⁻¹).measurableEmbedding) (S.penaltyWeight β)
  unfold noiseLink
  rw [integral_const_mul,h,← StepData.penaltyZ,inv_mul_cancel₀ (S.penaltyZ_pos β).ne']

lemma perLink_cont (U : Config G f) (t : S.SitesChoice) (e : Edge (Site c)) :
    Continuous (perLink S β U t e) := by
  unfold perLink
  exact continuous_finsetSum _ fun _ _ => continuous_const.mul (noiseLink_cont S β _)

lemma perLink_mass (U : Config G f) (t : S.SitesChoice) (e : Edge (Site c)) :
    (∫ v, perLink S β U t e v ∂G.probHaar) = 1 := by
  unfold perLink
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul,noiseLink_mass,mul_one]; exact S.patch.predictorMass_sum ..
  intro r _; exact ((noiseLink_cont S β _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _



private def atLink (U : Config G f) (t : S.SitesChoice) (e : Edge (Site c)) (v : G.El) : ℂ :=
    perLink S β U t e v
private def atSite (U : Config G f) (x : Site c) (r : S.patch.FrameTag) : ℂ := perSite S U x r
private def state (U : Config G f) (F : Config G c → ℂ) (t : S.SitesChoice) :=
    ∫ V, (∏ e, atLink S β U t e (V e)) * F V ∂prior G c

private lemma link_unit (U : Config G f) (t) (e) : (∫ v, atLink S β U t e v ∂G.probHaar) = 1 :=
    Eq.trans (integral_ofReal (𝕜:=ℂ) (f:=perLink S β U t e)) (by rw [perLink_mass]; rfl)

private lemma link_env (U : Config G f) (t) (e) : Envelope (atLink S β U t e) :=
  Envelope.compactC (Complex.continuous_ofReal.comp (perLink_cont S β U t e))

private lemma site_unit (h : S.patch.Branches S.kernel G) (U : Config G f) (x) :
    (∑ r, atSite S U x r) = 1 := by
  unfold atSite perSite; rw [← Complex.ofReal_sum,S.patch.frameMass_sum h,Complex.ofReal_one]

private lemma parts_back (U : Config G f) (F : Config G c → ℂ) (h : Envelope F) :
    back S β F U = ∑ t : S.SitesChoice, (∏ x, atSite S U x (t x)) * state S β U F t := by
  unfold back
  simp_rw [density_parts,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]; rfl
  intro t _
  refine Integrable.const_mul ?_ _
  apply Envelope.integrableC
  exact (Envelope.prodC _ (fun e (V : Config G c) => atLink S β U t e (V e))
    (fun e _ => (link_env S β U t e).comp_env (measurable_pi_apply _))).mulC h
end parts

def actualEdges (X : Set (Site c)) : Set (Edge (Site c)) := {e | e.1∈X ∧ e.1+step e.2∈X}
lemma read_edges {X : Set (Site c)} {Y : Type*} {F : Config G c → Y} (h : LocalOn X F) : Reads (actualEdges X) F :=
  fun U V he => h U V fun e hx hy => he (show e∈actualEdges X from ⟨hx,hy⟩)

section dep
variable {S β} {X : Set (Site c)} {F : Config G c → ℂ}

private lemma state_reads (h : S.patch.Branches S.kernel G) (he : Envelope F) (hp : LocalOn X F)
    (β : ℝ) (U : Config G f) : Reads X (state S β U F) := by
  intro t l hl
  apply pi_ignores (hF:=read_edges hp) he (link_unit S β U t) (link_unit S β U l) (link_env S β U t) (link_env S β U l)
  intro e hr
  unfold atLink perLink
  have hi : _ ∧ _ := show e.1∈X ∧ e.1+step e.2∈X from hr
  rw [connector_dep S h e t l (hl hi.1) (hl hi.2) (fun _ _ _ => rfl : Agrees _ U U) (fun _ _ _ => rfl)]

/-- Dependence of the result includes the masses (not just evaluation of a
single active choice). Asking for all endpoints in the indicated windows
ensures even the masked choices are covered. -/
lemma back_local (h : S.patch.Branches S.kernel G) (he : Envelope F) (hp : LocalOn X F) (β : ℝ)
    (Y : Set (Site f)) (hq : ∀ x∈X, window (S.ratio.embed x) (reach S.patch) ⊆ Y) :
    LocalOn Y (back S β F) := by
  intro U V hu
  have hh (x : Site c) (hx : x∈X) : Agrees (window (S.ratio.embed x) (reach S.patch)) U V :=
    agrees_mono hu (hq x hx)
  have hz (t : S.SitesChoice) : state S β U F t = state S β V F t := by
    apply pi_ignores (hF:=read_edges hp) he (link_unit S β U t) (link_unit S β V t) (link_env S β U t) (link_env S β V t)
    intro e hr
    unfold atLink perLink
    have hi : e.1∈X ∧ e.1+step e.2∈X := hr
    rw [connector_dep S h e t t rfl rfl (hh _ hi.1) (hh _ hi.2)]
  rw [parts_back S β U F he,parts_back S β V F he]
  simp_rw [hz]
  apply sum_ignores (state_reads h he hp β V) (site_unit S h U) (site_unit S h V)
  intro x hx; funext t
  unfold atSite perSite
  rw [(site_dep S h x (hh x hx) t).2]

/-- Given the fine links. For arbitrary bounded local observables, not just
field insertions. Doesn't yet assert multiplication upon running several
levels: then need *cones* disjoint at each step. -/
lemma back_factors {W : Config G c → ℂ} {Y : Set (Site c)}
    (h : S.patch.Branches S.kernel G) (he : Envelope F) (hw : Envelope W)
    (hp : LocalOn X F) (ht : LocalOn Y W) (hd : Disjoint X Y) (β : ℝ) :
    back S β (F*W) = back S β F * back S β W := by
  funext U; rw [parts_back S β U (F*W) (show Envelope (F*W) from he.mulC hw), Pi.mul_apply, parts_back S β U _ he, parts_back S β U _ hw]
  have hh (t : S.SitesChoice) : state S β U (F*W) t = state S β U F t * state S β U W t := by
    have hx : Disjoint (actualEdges X) (actualEdges Y) := Set.disjoint_left.mpr
      (fun i hi hk => Set.disjoint_left.1 hd (show i.1∈X ∧ _ from hi).1 (show i.1∈Y ∧ _ from hk).1)
    exact pi_independent (read_edges hp) (read_edges ht) hx (link_unit S β U t) (link_env S β U t) he hw
  simp_rw [hh]; exact sum_independent (state_reads h he hp β U) (state_reads h hw ht β U) hd (site_unit S h U)

open Cells

/-- With gauge covariance, actual cone growth in fine sites. Applicable at
every level in the history. -/
lemma back_cylinder (h : S.patch.Branches S.kernel G) {o : Site c} {R : ℕ}
    (he : Interior (window o R) F) (β : ℝ)
    (hg : ∀ U V t, S.density (G:=G) β (gauge t U) (gauge (t ∘ S.ratio.embed) V)=S.density β U V) :
    Interior (window (S.ratio.embed o) (S.ratio.count.val*R+reach S.patch)) (back S β F) := by
  have hF := cylinder_env he
  have hk := S.isKernel h β
  have hb := back_env hk hF
  refine ⟨fun t U => ?_, hb.meas, back_local h hF he.localSites β _ ?_, hb.cost⟩
  · let s := t ∘ S.ratio.embed
    have hv := back_natural hk hF (gauge t) (gauge s) (prior_gauge s) fun U V => hg U V t
    rw [show F ∘ gauge s = F from funext fun V => he.gauge s V] at hv
    exact (congr_fun hv U).symm
  intro x hx y hy
  exact window_add (window_embed _ hx) hy
end dep
end YM.Push.GridApprox
