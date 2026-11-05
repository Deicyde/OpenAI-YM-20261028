import YM.Contacts.Layers.Readout

/-! # Closure for repeated signed projections without altering the label, theory or scheme

Complete the proof of layer stability, with the full root output gain **through h+1** on
the hierarchy residual. This is a rate bound allowing ε power losses which includes the finer
scale of every element in the cluster. Strict separation and log-layer hypotheses only. Later,
use the clearance and these results uniformly in finitely many trees.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set Metric MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {W : Type}
variable {F : Extraction.Order} {Z : Final C F S} {M : Devices Z.sector.derivatives}
variable {φ : Filter W} {T : W → ℝ} {c d r s u : ℝ}
variable {x : W → E4} {A : Set (W → E4)} {w d' : ℕ}
local notation "D" => M.basis
local notation "EP" => W → Expression Z.sector.derivatives
variable {e f : W → Expression Z.sector.derivatives}

lemma loose_diff {s : ℝ} (h : ∃ c, Fine M φ T A s c e) (he : ∃ c, Fine M φ T A s c f) : ∃ c, Fine M φ T A s c (e-f):= by
  obtain ⟨c,h⟩:=h; obtain ⟨d,he⟩:=he; exact ⟨max c d,.diff (h.mono (le_max_left ..)) (he.mono (le_max_right ..))⟩
lemma Fits.down (h : Fits M φ d' x A) (hp : w ≤ d') : Fits M φ w x A:= fun y hy=> (h y hy).mono fun _ h=> h.trans (M.antitone_clearance hp)

def maxFee (M : Devices Z.sector.derivatives) (w : ℕ) := ∑ i:Fin (w+1), probeFee M i
def statedProject (M : Devices Z.sector.derivatives) (w : ℕ) (x : W → E4) (e : W→ Expression Z.sector.derivatives) (i : W) := M.replaceAt (x i) w (e i)

variable (hT : Tendsto T φ atTop)
include hT

lemma precision_project (h : Precision Z M φ T A u c e) (hf : Fits M φ w x A) (hx : x∈ A)
   (hU : 0 ≤ u)(he : ∃ c,Fine M φ T A 1 c e) : Fine M φ T A u (c+maxFee M w+w*u) (statedProject M w x e) := by
  apply Fine.field hT hx (p:=fun i=> M.project (x i) w (e i))
  simp_rw [← M.project_through, add_sub_cancel_right]; refine RateLE.sum hT fun j hj=>?_
  apply rate_linear (LinearMap.toContinuousLinearMap (Z.sector.derivatives.rise (show j.val ≤ w from Nat.le_of_lt_succ j.isLt))) hT
    (f:=fun i=> M.row (x i) j (e i))
  refine (Against.row M hT e h hU zero_le_one (hf.down (Nat.le_of_lt_succ j.isLt)) he).mono ?_
  rw [mul_one]; exact add_le_add_right (Finset.single_le_sum (f:=fun j:Fin (w+1)=> probeFee M j) (fun j _=>Finset.sum_nonneg (f:=fun i:(M.tests j).probes=>(sigma i.val.letter:ℝ)) fun _ _=>Nat.cast_nonneg _) hj) _

variable [φ.NeBot] (H : Services C F S)
variable (ha : Habitat φ T s x A) (hx : x∈A)
include H ha hx
lemma Funds.outputs (h : Funds Z M φ T A s c e) (hs : 0 ≤ s) (hv : s ≤ 1) (hp : Fits M φ w x A) : RateLE φ T (fun i=> M.row (x i) w (e i)) (c-w*s):= by
  rcases hs.eq_or_lt with h'|hs
  · subst s; simpa only [mul_zero, add_zero, sub_zero] using Against.row M hT e (h.tests hT H le_rfl le_rfl hv) le_rfl le_rfl hp h.loose -- dot order inspect
  obtain ⟨g,hh,hq⟩:= (Matchable.layer hT H ha hs le_rfl hv hx h).replaces (c-w*s-probeFee M w)
  have hw:= Against.row M hT (e-g) hq le_rfl zero_le_one hp (loose_diff h.loose ((hh.fine hT hx).increase_layer hv))
  rw [mul_one,sub_add_cancel] at hw
  refine (hw.add (hh.row hT hs.le w) hT).congr ?_
  filter_upwards with i; simp
lemma Funds.allProjected (h : Funds Z M φ T A s c e) (hs : 0 ≤ s)(hv : s ≤ 1)(hp : Fits M φ w x A) : Fine M φ T A s c (statedProject M w x e) := by
  refine Fine.germ (Fine.sum' (p:=Finset.univ) (E:=fun j:Fin (w+1)=>fun i=>M.insertRow (x i) j (e i)) (fun j _=>?_))
     (Eventually.of_forall fun i=> M.replace_sum (x i) w (e i))
  exact Fine.field hT hx (h.outputs hT H ha hx hs hv (hp.down (Nat.le_of_lt_succ j.isLt)))

/-- Signed ancestor transfer. One gain for *each* such move informed by descendants. -/
lemma Funds.drop (h : Funds Z M φ T A s c e) (hp : Fits M φ w x A) (hs : u ≤ s)(hv : s ≤ 1)(hu : 0 ≤ u) : Funds Z M φ T A u (c-(w+1:ℝ)*(s-u)) (e-statedProject M w x e) := by
  rcases hs.eq_or_lt with h'|hs
  · subst u; rw [sub_self,mul_zero,sub_zero,sub_eq_add_neg]; exact h.plus hT ((h.allProjected hT H ha hx hu hv hp).funds hv).minus
  refine ⟨loose_diff h.loose ((h.allProjected hT H ha hx (hu.trans hs.le) hv hp).increase_layer hv),fun q=>?_⟩
  let v := min q (q - maxFee M w - w*u)
  obtain ⟨g,hh,hq⟩:= (Matchable.layer hT H ha hs hu hv hx h).replaces v
  refine ⟨(g-statedProject M w x g), hh.residue hT hu hs.le w hx,?_⟩
  have he : Precision Z M φ T A u q (statedProject M w x (e-g)):= by
     apply Against.mono ((precision_project hT hq hp hx hu (loose_diff h.loose ((hh.fine hT hx).increase_layer hv))).tests (Z:=Z) hT H hu (hs.le.trans hv)) le_rfl _ (by rfl)
     linarith only [show v ≤ q-maxFee M w-w*u from min_le_right ..]
  rw [show e-statedProject M w x e-(g-statedProject M w x g) = e-g-statedProject M w x (e-g) from funext fun i=>by simp only [Pi.sub_apply,statedProject,map_sub]; abel]
  exact Against.diff (Against.mono hq le_rfl (min_le_left ..) (by rfl)) he hT
lemma Funds.coarsen (h : Funds Z M φ T A s c e) (hs : u ≤ s)(hv : s ≤ 1)(hu : 0 ≤ u) : Funds Z M φ T A u c e:=
    hs.eq_or_lt.elim (fun hh=> hh ▸ h) fun he=> Matchable.fall hT H ha he hu hv hx h
end YM.Contacts.Layers
