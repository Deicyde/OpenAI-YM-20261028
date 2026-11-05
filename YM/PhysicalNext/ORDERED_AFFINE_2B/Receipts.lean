import YM.Further.CURVED_GAUSSIAN_JETS.Offices
import YM.PhysicalNext.ORDERED_AFFINE_2B.Lift
import YM.PhysicalNext.ORDERED_AFFINE_2B.Whole

/-!
# Transfer the purchased Street (CGJ kernel jets) to the whole SC alphabet

Slower width (explicit post-L loss); price gap/order*δ/mass
can afford the additional trunks, even if F had no active links
somewhere/small period. No exponential price per terrain decision. Use
true branch identity on a neighborhood from `Mapper` (not just jet
matching from equality at a single point). Output later pays ALL queries
including across the larger array. This file only numerical bounds under
that identity before buying the actual sectors, not claiming localization
of the matrix log itself by anchors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole.Receipts
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree AnalyticBridge AnalyticBridge.Covariance
open AnalyticBridge.ResetIncome SectorTools.ActualScalar
open Further Further.CurvedGaussianJets Jets ChangeV
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f}
    {v : CurvedGaussianJets.Prices}
    {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    {a : K → Site f} {q k M D : ℕ} {δ t C : ℝ} {o : Site f} {ht : 0 ≤ t}
    {Q : Directions G c → Prop} {V : Config G c}

def revised (v : CurvedGaussianJets.Prices) (M : ℕ) : CurvedGaussianJets.Prices where
  width := min (spare v) v.width
  gap := min 1 v.gap
  mass := max 1 v.mass
  tags := M
  width_pos := lt_min (spare_pos _) v.width_pos
  gap_pos := lt_min zero_lt_one v.gap_pos
  mass_pos := v.mass_pos.trans_le (le_max_right ..)

lemma gives (e : I⊕J ≃ K) {B : CurvedGaussianJets.Table I} (h : Fits (a ∘ e ∘ Sum.inl) v B)
    (hM : Push.Uniform.Multiplicity a M) : Fits a (revised v M) (Joint.place e (Joint.join B 1)) := by
  apply Rates.completes e _ h.symm _ (min_le_left ..) (le_max_left ..) hM
  · exact Rows.bigger (Rows.slower h.entries (min_le_right ..)) (le_max_right ..)
  intro i; exact (mul_le_mul_of_nonneg_right (min_le_right ..) (Joint.dot_nonneg _)).trans (h.floor i)

def smaller (v : CurvedGaussianJets.Prices) (M k : ℕ) := spare (revised v M) / (1+k)
lemma small_pos (v : CurvedGaussianJets.Prices) (M k : ℕ) : 0 < smaller v M k := div_pos (spare_pos _) (by positivity)

omit [DecidableEq I] in
lemma shrunk {a : I→ Site f} {A : Jets.Field G c I} {hδ : 0<δ} (M : ℕ) (h : Street v (rule a o q ht hδ) k Q A V C) :
    let v' := revised v M; let s := rule a o q ht (small_pos v M k)
    Cash s v'.speed k Q V A C ∧ 0 ≤ s.width (spare v') k := by
  intro v' s; let α := smaller v M k; have hp : 0<α := small_pos ..
  let s' := rule a o q ht hδ; have hd : 0<δ := hδ
  constructor
  · intro l hl hQ
    obtain ⟨h₁,h₂⟩ := h.cash l hl hQ
    have he : s.width v'.speed l.length ≤ s'.width v.speed l.length := by
      have ht' : s'.width (spare v) k ≤ s'.width (spare v) l.length := s'.width_le _ _ _ hl
      have hu := four_spare v
      have hm : 0 ≤ spare v- l.length*δ := h.room.trans ht'
      have he := (v').speed_le.trans (show (v').width ≤ spare v from min_le_left ..); have hg := spare_pos v
      change v'.speed - l.length*α ≤ v.speed - l.length*δ
      have hx : 0 ≤ (l.length:ℝ)*α := by positivity
      linarith only [he,hu,hx,hm,hg]
    have hh (B : CurvedGaussianJets.Table I) (hB : s'.Costs v.speed l.length B C) : s.Costs v'.speed l.length B C := by
      intro i; apply (Finset.sum_le_sum (fun j _=>?_)).trans (hB i); unfold Progress.StationaryScenes.Green.wt; gcongr
    exact ⟨hh _ h₁,hh _ h₂⟩
  change 0 ≤ spare v'- k*(spare v'/(1+k))
  have hz : (1+(k:ℝ))*α = spare v' := by unfold α v' smaller; field_simp
  change 0 ≤ spare v'-(k:ℝ)*α; linarith

lemma budget (e : I⊕J ≃ K) {A : Jets.Field G c I} {hδ : 0<δ} (h : Street v (rule (a ∘ e ∘ Sum.inl) o q ht hδ) k Q A V C)
    (hM : Push.Uniform.Multiplicity a M) : Street (revised v M) (rule a o q ht (small_pos v M k)) k Q (fun U=>Joint.place e (Joint.join (A U) 1)) V (max 1 C) := by
  obtain ⟨hp,hr⟩ := shrunk M h
  have hh := completed ht (small_pos v M k) (show Stock _ Q _ k A V C from ⟨h.has,h.good,hp⟩)
  exact ⟨gives e h.base hM,hh.cash,hr,hh.good,hh.has⟩

lemma consume {a : I→Site f} {s : Weights a} {A B : Jets.Field G c I} (h : Street v s k Q A V C) (he : A =ᶠ[𝓝 V] B) :
    Street v s k Q B V C := by
  refine ⟨(he.self_of_nhds ▸ h.base), ?_,h.room,?_,h.has⟩
  · intro l hl hQ; rw [jet_eq he.symm]; exact h.cash l hl hQ
  intro i j; apply (h.good i j).congr_of_eventuallyEq
  have ht : Tendsto (increment V) (𝓝 0) (𝓝 V) := by simpa only [Multi.Puff.inc_zero] using (show Continuous (increment V) by unfold increment; fun_prop).tendsto 0
  filter_upwards [ht.eventually he.symm] with x hx; rw [hx]

-- cost per native site includes FULL canonical contents.
def things (G : Gauge) := Fintype.card Axis * Fintype.card G.ColorIndex
lemma numerous (G : Gauge) (f : Side) : Push.Uniform.Multiplicity (initial G f) (things G) := by
  intro o; unfold things; rw [←Fintype.card_prod,←Finset.card_univ]
  let p (i : Thing G f) : Axis×G.ColorIndex := (i.1.2,i.2)
  apply Finset.card_le_card_of_injOn p (fun _ _=>Finset.mem_univ _) (fun i hi j hj he=>?_)
  have h : i.1.1 = j.1.1 := Eq.trans (a:=initial G f i) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2.symm
  exact Prod.ext (Prod.ext h (congr_arg Prod.fst he)) (show (p i).2=(p j).2 from congr_arg Prod.snd he)
end YM.PhysicalNext.OrderedAffine2B.Whole.Receipts
