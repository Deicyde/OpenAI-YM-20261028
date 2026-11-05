import YM.RG08.Ballast.Charge
import YM.Analysis.Homogeneous

/-!
# Formal coefficient vertices in canonical positions

One free translation CENTER for vacuum vertices, r WO potentials.
Args relative to center. Can also be used with specified source center,
not handled in this module. taylor coefficients (not derivatives), anchor
multiplicity is the volume, NO thermodynamic conclusions implicit.
Symbols via Stationary.Picture below. Real normalization to projected qpta
packet later, not receiving actual remainder estimates here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Push.AbsoluteSums Finset Function
open UVExt.Paths Stationary
open scoped Classical Topology ContDiff
variable {α β ι : Type} {r : ℕ} {w w' C A B : ℝ} {m : Side}

abbrev Beads (α : Type) (r : ℕ) := Fin r → Cover × α
abbrev Shale (α : Type) (r : ℕ) := Beads α r → ℝ
abbrev PAC (α : Type) (m : Side) := Corn (Co m α)

def girth (b : Beads α r) := ∑ i,size (b i).1
-- moment lane with explicit exponential reserve
def ling (w : ℝ) (b : Beads α r) := Real.exp (w*girth b)
lemma ling_pos (w : ℝ) (b : Beads α r) : 0 < ling w b := Real.exp_pos _
lemma ling_one (h : 0≤w) (b : Beads α r) : 1 ≤ ling w b := Real.one_le_exp (mul_nonneg h (Nat.cast_nonneg _))
abbrev Glow (f : Shale α r) (w A : ℝ) := Charge (ling w) f A
theorem glow_moment {h : Shale α r} (v : Glow h w C) (hw : 0<w) (k : ℕ) :
    SumBudget (fun b => (1+(girth b:ℝ))^k*‖h b‖)
      ((w⁻¹^k*k.factorial*Real.exp w)*C) := by
  have hq : 0 ≤ w⁻¹^k*k.factorial*Real.exp w := by positivity
  apply budget_mono (budget_scale hq v) (fun _ => by positivity); intro i
  have he : 0 ≤ 1+(girth i:ℝ) := by positivity
  refine (mul_le_mul_of_nonneg_right (polynomial_price hw he k) (norm_nonneg (h i))).trans_eq ?_
  rw [mul_add, mul_one,Real.exp_add, ling]; ring
lemma glow_less {F : Shale α r} (hf : Glow F w A) (hy : w' ≤ w) (hb : A ≤ B) : Glow F w' B :=
  hf.mono (fun i => (ling_pos w' i).le) (fun _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy (by positivity))) hb

variable {F H : Shale α r}

def silks (z : Site m) (x : Beads α r) (i : Fin r) : Co m α := (z+wrap m (x i).1,(x i).2)
def rosary (v : Fin r → PAC α m) (z : Site m) (x : Beads α r) : ℝ := ∏ i,v i (silks z x i)
section paid
variable [Fintype α]

lemma rosary_bill (v : Fin r → PAC α m) (z) (x) : ‖rosary v z x‖ ≤ ∏ i, ‖v i‖ := by
  unfold rosary; rw [norm_prod]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> norm_le_pi_norm (v i) _)
lemma bead_summable (F : Shale α r) (v : Fin r → PAC α m) (hf : Summable F) (z) :
    Summable (fun x => F x*rosary v z x) := sum_bounded hf (rosary_bill v z)

def stitch (f : Shale α r) (m : Side) (z : Site m) : Tensor.T (PAC α m) ℝ r where
    toMultilinearMap := recording (pool f (silks z))
    cont := by
      show Continuous (fun v => recording (pool f (silks z)) (v : Fin r → PAC α m))
      simp_rw [recording_apply]
      fun_prop

lemma stitch_apply (h : Summable F) (v : Fin r → PAC α m) (z : Site m) :
    stitch F m z v=∑' j,F j*rosary v z j := by
  change recording _ _=_; rw [recording_apply]
  let g (i : Fin r→Co m α) := ∏ k, v k (i k)
  have hv (i : Fin r→Co m α) : ‖g i‖ ≤ ∏ k,‖v k‖ := by
    rw [show g i=_ from (rfl:g i=∏ k,v k (i k)),norm_prod]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun k _=> norm_le_pi_norm (v k) _)
  have he := pool_total g (silks z) h hv; rw [tsum_fintype] at he; simp_rw [mul_comm _ (pool _ _ _)]
  exact he

def recital (F : Shale α r) (m : Side) : Tensor.T (PAC α m) ℝ r := ∑ z, stitch F m z
def stanza (F : Shale α r) (m : Side) := Tensor.diagonal (recital F m)
lemma recital_eval (v : Fin r → PAC α m) (h : Summable F) : recital F m v=∑ z, ∑' j,F j*rosary v z j := by
  unfold recital; rw [_root_.sum_apply]; simp_rw [stitch_apply h]
lemma stanza_apply (B : PAC α m) (h : Summable F) : stanza F m B=∑ z, ∑' j,F j*rosary (fun _=> B) z j := recital_eval _ h
lemma stanza_smooth (F : Shale α r) (m : Side) : ContDiff ℝ ω (stanza F m) := Tensor.diag_smooth ..
lemma stanza_homo (F : Shale α r) (t : ℝ) (x : PAC α m) : stanza F m (t • x)= t^r*stanza F m x := Tensor.homogeneous ..
@[simp] lemma recital_zero (α : Type) [Fintype α] (r : ℕ) (m : Side) : recital (0:Shale α r) m=0 := by ext1 v; rw [recital_eval v (show Summable (0:Shale α r) from summable_zero)]; simp
lemma recital_add (hf : Summable F) (hh : Summable H) (m : Side) : recital (F+H) m=recital F m+recital H m := by
  ext1 v
  have hu : Summable (F+H) := hf.add hh
  rw [_root_.add_apply,recital_eval _ hu,recital_eval _ hf,recital_eval _ hh, ← sum_add_distrib]
  apply sum_congr rfl; intro z _; simp_rw [Pi.add_apply,add_mul]; exact (bead_summable _ v hf z).tsum_add (bead_summable _ v hh z)
lemma recital_scale (a : ℝ) (hf : Summable F) (m : Side) : recital (a • F) m=a • recital F m := by
  ext1 v
  have he : Summable (a • F) := hf.mul_left _
  rw [_root_.smul_apply,recital_eval _ he,recital_eval _ hf,smul_eq_mul,mul_sum]
  apply sum_congr rfl; intro z _; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc]; rw [tsum_mul_left]
lemma recital_sub (hf : Summable F) (hh : Summable H) (m : Side) : recital (F-H) m=recital F m-recital H m := by
  have hz : Summable (-H) := hh.neg
  rw [sub_eq_add_neg,sub_eq_add_neg, recital_add hf hz, ← neg_one_smul ℝ H,recital_scale _ hh,neg_one_smul]
lemma recital_sum (s : Finset ι) (F : ι→Shale α r) (h : ∀ i∈s,Summable (F i)) (m : Side) :
    recital (∑ i∈s,F i) m=∑ i∈s,recital (F i) m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have he (j) (hj : j∈s) := h j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi,recital_add (h i (mem_insert_self ..)), ih he]
    rw [show (∑ j∈s,F j)=(fun b => ∑ j∈s,F j b) from funext fun _=>Finset.sum_apply ..]
    exact summable_sum he
@[simp] lemma stanza_zero (m : Side) : stanza (0:Shale α r) m=0 := by simp [stanza]; rfl
lemma stanza_add (hf : Summable F) (hh : Summable H) (m : Side) : stanza (F+H) m=stanza F m+stanza H m := by
  unfold stanza; rw [recital_add hf hh]; rfl
lemma stanza_sub (hf : Summable F) (hh : Summable H) (m : Side) : stanza (F-H) m=stanza F m-stanza H m := by
  unfold stanza; rw [recital_sub hf hh]; rfl
lemma stanza_scale (a : ℝ) (hf : Summable F) (m : Side) : stanza (a • F) m=a • stanza F m := by
  unfold stanza; rw [recital_scale a hf]; rfl
lemma stanza_sum (s : Finset ι) (F : ι→Shale α r) (h : ∀ i∈s,Summable (F i)) (m : Side) :
    stanza (∑ i∈s,F i) m=∑ i∈s,stanza (F i) m := by
  funext x; unfold stanza; rw [recital_sum s F h]; unfold Tensor.diagonal; rw [_root_.sum_apply,Finset.sum_apply]

lemma recital_pool (f : ι → ℝ) (hf : Summable f) (m : Side) (s : ι → Beads α r) (v : Fin r → PAC α m) :
    recital (pool f s) m v=∑ z,∑' j,f j*rosary v z (s j) := by
  rw [recital_eval]
  · apply sum_congr rfl; intro z _; exact pool_total _ _ hf (rosary_bill v z)
  exact (hf.hasSum.tsum_fiberwise s).summable
end paid
end YM.RG08
