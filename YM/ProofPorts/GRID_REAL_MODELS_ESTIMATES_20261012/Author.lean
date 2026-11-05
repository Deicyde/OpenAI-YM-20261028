import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.Next.BOUNDARY.Synchronize
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Comparison
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Hybrid
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Marginal
import YM.ProofPorts.GRID_REAL_MODELS_ESTIMATES_20261012.Comparison
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Palette
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.UVNext.PHASE_COARSE_ERROR.Kiln

/-!
# Write one coherent map of local substitutes at an actual station k

Beyond just obtaining `HasModels`, produce it with a *common* intermediate
k holding for all fields and word lengths, support control for the
substitutes on both coarse and fine sites. This is useful e.g. to run
 without separating the Θ partners' estimates at different k's or
even splitting a reconstruction client using rotated bases/stencils or many
translations into separately assembled grill markets. No assumption that one
can just intersect independent useable sets of k's. Also keeps exact physical
scale of the unit, everywhere sup bounds and ordinary star law. We'll even
make this covariant simultaneously under Signed (later file).

Native radius at k may grow; the resulting MODEL prices are nevertheless
paid including their physical support budget from any finer cutoff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.GridRealModelsEstimates20261012

open RG Wilson Lattice Cells MeasureTheory Filter Set Function
open Push.GridApprox ProjectorNext.RMirror
open Next.UVStress (Coarse region)
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {f g : Extraction.Order}
variable {h k j N p r d : ℕ}

abbrev costSize (C : Family G) (v : C.label d) : ℝ := (C.labels.level d).coeffSize v

abbrev Arrays (C : Family G) (k : ℕ) := (N p : ℕ) → Config G (C.side k p) → ℂ

abbrev Script (C : Family G) (k d : ℕ) := C.label d →ₗ[ℂ] Arrays C k

/-- Certify any real coherent set of comparison fields. This sees only
auxiliary bounded substitutes, so does not require true calibration
transforms/coefficient histories for these *k-readouts*. `accurate` still
compares to the literal N calibration. Its estimate is on the **joint**
root of that actual law, not ordinary sup on the difference.
-/
structure Authored (C : Family G) (f : Extraction.Order) (t : h ≤ k)
    (r : ℕ) (A ε : ℝ) (Y : Script C k d) : Prop where
  eligible : room C.path.levels h k r
  budget : 1 ≤ A
  circle (N p : ℕ) (v : C.label d) : Interior (region (C.side k p) r) (Y v N p)
  texts (N p : ℕ) (v : C.label d) (U) : ‖Y v N p U‖ ≤ A*costSize C v
  stars (N p : ℕ) (v : C.label d) (U) : star (Y v N p U)=Y (star v) N p U
  unit (N p : ℕ) : Y (C.refUnit d) N p=1
  accurate : f.late fun N p => ∃ hk : k ≤ N, ∀ v,
      (tilesAt C.S p (t.trans hk)).rootTest (C.beta N p) (backTo C.path N p hk (Y v N p)-C.seen ⟨d,v⟩ 0)
        ≤ ε*costSize C v

lemma region_subset {r R : ℕ} (n : Side) (hr : r ≤ R) : region n r ⊆ region n R :=
  Set.image_mono fun _ ha => box_larger ha hr

lemma Authored.loosen {Y : Script C k d} {t : h ≤ k} {r R : ℕ} {A ε B : ℝ}
    (H : Authored C f t r A ε Y) (hr : r ≤ R) (hp : room C.path.levels h k R) (hA : A ≤ B) :
    Authored C f t R B ε Y where
  eligible := hp
  budget := H.budget.trans hA
  circle N p v := (H.circle N p v).enlarges (region_subset _ hr)
  texts N p v U := (H.texts N p v U).trans (mul_le_mul_of_nonneg_right hA (Work.G08.size_nonneg ..))
  stars := H.stars
  unit := H.unit
  accurate := H.accurate

lemma Authored.keep {Y : Script C k d} {t : h ≤ k} {r : ℕ} {A ε : ℝ}
    (H : Authored C f t r A ε Y) (hp : Next.BOUNDARY.Refines g f) : Authored C g t r A ε Y where
  eligible := H.eligible
  budget := H.budget
  circle := H.circle
  texts := H.texts
  stars := H.stars
  unit := H.unit
  accurate := hp.late H.accurate



section linear

lemma interior_sum {n : Side} {ι : Type*} {X : Set (Site n)} (s : Finset ι)
    (F : ι → Config G n → ℂ) (hF : ∀ i∈s, Interior X (F i)) : Interior X (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (show Interior X 0 from Interior.constant _ (0:ℂ))
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact
      (hF i (Finset.mem_insert_self ..)).plus (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

lemma backTo_linear (N p : ℕ) (e : k ≤ j) (Y : Config G (C.side k p) → ℂ) (a : ℂ) :
    backTo C.path N p e (a • Y) = a • backTo C.path N p e Y := by
  induction j,e using Nat.le_induction with
  | base => simp only [backTo_self]
  | succ j w ih =>
    rw [backTo_next C.path N p w, ih, backTo_next C.path N p w]
    funext U
    simp_rw [Push.GridApprox.back, Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, integral_const_mul]
    rfl

lemma backTo_sum {ι : Type*} (s : Finset ι) (N p : ℕ) (e : k ≤ j) (Y : ι → Config G (C.side k p) → ℂ)
    (he : ∀ i ∈ s, Envelope (Y i)) :
    backTo C.path N p e (∑ i ∈ s, Y i) = ∑ i ∈ s, backTo C.path N p e (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact backTo_const C.path N p e 0
  | insert i s hi ih =>
    have ht a (ha : a∈s) := he a (Finset.mem_insert_of_mem ha)
    have hh : Envelope (∑ a∈s, Y a) := by
      have hf := Envelope.sumC s Y ht
      simpa only [← Finset.sum_apply] using hf
    rw [Finset.sum_insert hi, Finset.sum_insert hi, backTo_add C.path N p e (he i (Finset.mem_insert_self ..)) hh, ih ht]

lemma backTo_linSum {ι : Type*} [Fintype ι] (N p : ℕ) (e : k ≤ j) (Y : ι → Config G (C.side k p) → ℂ)
    (a : ι → ℂ) (he : ∀ i, Envelope (Y i)) :
    backTo C.path N p e (∑ i, a i • Y i) = ∑ i, a i • backTo C.path N p e (Y i) := by
  have hc i : Envelope (a i • Y i) := (Envelope.constC _).mulC (he i)
  rw [backTo_sum Finset.univ _ _ e _ (fun i _ => hc i)]; simp_rw [backTo_linear N p e]

end linear

private def inscribe (Z : Ind C d → Arrays C k) : Script C k d where
  toFun v := ∑ i, v i • Z i
  map_smul' a v := by simp [Finset.smul_sum,smul_smul]
  map_add' v w := by simp [add_smul,Finset.sum_add_distrib]

private lemma inscription (Z : Ind C d → Arrays C k) (v : C.label d) (N p : ℕ) :
    inscribe Z v N p = ∑ i, v i • Z i N p := by
  simp only [inscribe,LinearMap.coe_mk,AddHom.coe_mk, Finset.sum_apply]; rfl

private lemma author_book {t : h ≤ k} {A ε : ℝ} {Z : Ind C d → Arrays C k}
    (H : C.Makes) (hr : room C.path.levels h k r) (hA : 1 ≤ A)
    (hL : ∀ i N p, Interior (region (C.side k p) r) (Z i N p))
    (hC : ∀ i N p U, ‖Z i N p U‖ ≤ A ∧ star (Z i N p U)=Z i N p U)
    (ho : ∀ N p U, Z 0 N p U = oneColor C d)
    (hp : ∀ i : Ind C d, f.late fun N p => ∃ hk : k ≤ N,
      (tilesAt C.S p (t.trans hk)).rootTest (C.beta N p)
        (backTo C.path N p hk (Z i N p)-C.seen (swatch C d i) 0) ≤ ε) :
    Authored C f t r A ε (inscribe Z) where
  eligible := hr
  budget := hA
  circle N p v := by rw [inscription]; exact interior_sum _ _ fun _ _ => (hL ..).scale _
  texts N p v U := by
    rw [inscription, Finset.sum_apply]
    unfold costSize Labels.Frame.coeffSize; rw [mul_comm,Finset.sum_mul]
    apply (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
    intro i _; simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hC i N p U).1 (norm_nonneg _)
  stars N p v U := by
    simp_rw [inscription,Finset.sum_apply,star_sum,Pi.smul_apply,star_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [(hC i N p U).2]; rfl
  unit N p := by
    funext V
    rw [inscription]
    let x : ℂ := (C.S.a (C.ref d):ℂ)^d
    change (∑ i : Ind C d, ((x • (C.labels.level d).e0) i) • Z i N p) V = 1
    rw [Finset.sum_apply, Finset.sum_eq_single (0 : Ind C d)]
    · simp only [Pi.smul_apply,smul_eq_mul,ho,Labels.Frame.e0, Pi.single_eq_same,mul_one]
      exact mul_inv_cancel₀ (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'))
    · intro i hi he; simp [Labels.Frame.e0,he]
    simp
  accurate := by
    have hm i := hp i
    unfold Extraction.Order.late at *
    filter_upwards [eventually_all.mpr hm] with j hj
    filter_upwards [eventually_all.mpr hj, f.mesh.cofinal.eventually (Stock.clear_interior C H h d)] with n hn hw
    obtain ⟨hs,hV⟩ := hw
    let p := f.per j; let N := f.mesh n
    have hk : k ≤ N := (hn 0).choose
    let T := tilesAt C.S p (t.trans hk)
    refine ⟨hk,fun v => ?_⟩
    let Y i := backTo C.path N p hk (Z i N p)
    let U (i : Ind C d) : Config G (C.side N p) → ℂ := C.seen (swatch C d i) 0
    have hu (i : Ind C d) : Interior (T.chamber 0) (Y i) :=
      (origin_local C t hk (hL ..)).enlarges (origin_fits C p t hk hr)
    have hd (i : Ind C d) : Interior (T.chamber 0) (Y i-U i) :=
      Next.UVStress.minus (hu i) (hV p 0 ((swatch C d i).2))
    change T.rootTest (C.beta N p) (backTo C.path N p hk _ - C.seen _ 0) ≤ _
    rw [inscription, backTo_linSum N p hk (fun i => Z i N p) v (fun i => cylinder_env (hL ..)),
      show C.seen ⟨d,v⟩ (0:Site (C.side N p)) = _ from seen_combination v N p 0]
    change T.rootTest (C.beta N p) ((∑ i,v i • Y i)-(∑ i,v i • U i)) ≤ _
    simp_rw [← Finset.sum_sub_distrib,← smul_sub]
    apply (Next.Extract.rooted T _ (seamless H ..) _ (fun i => Y i-U i) v (fun i _ => hd i)).2.trans
    unfold costSize Labels.Frame.coeffSize; rw [mul_comm ε,Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hn i).choose_spec (norm_nonneg _)





end YM.ProofPorts.GridRealModelsEstimates20261012
