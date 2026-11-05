import Mathlib.Data.Set.Finite.List
import YM.Further.CURVED_GAUSSIAN_JETS.RailV
import YM.Further.CURVED_GAUSSIAN_JETS.Truncated
import YM.Further.CURVED_GAUSSIAN_JETS.Weights


/-!
# Slab derivatives of actual transported cut series

Differentiate the actual cut table; true walk-length budget uniform at every
truncation (including when it has infinitely many coincident label paths!).
Regrouping to identify derivatives doesn't identify support labels for a gas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations
open Green (wt)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} (r : Ratio c f) (s : Signed) (N : ℕ) {W : PathData G}
    {K σ w C Λ : ℝ} {p : Clip} {k : ℕ} (hb : W.Bounds p σ C Λ) (hK : ExpReceipt G (k+1) K)

local instance : Finite Lattice.Step := Finite.of_injective (fun i : Lattice.Step => (i.dir,i.neg)) (by rintro ⟨a,b⟩ ⟨c,d⟩ h; cases Prod.mk.inj h; congr)

def rides := (List.finite_length_le Lattice.Step N).toFinset

def bundle (W : PathData G) (a b : Cell f) (p : Walk) (i : ℕ) := if (W.row a.2 i).2.walk=p then Cut.tick W N a b i else 0

include hb in
lemma grouped (a b : Cell f) (L : Walk → ℝ) : HasSum (fun i=> Cut.tick W N a b i * L (W.row a.2 i).2.walk)
    (∑ p∈rides N, (∑' i, bundle N W a b p i)*L p) := by
  have hs (p : Walk) : Summable (bundle N W a b p) := Summable.of_norm_bounded ((Cut.sum_tick (N:=N) hb a b).1.norm) (fun i => by unfold bundle; split; rfl; exact norm_zero.trans_le (norm_nonneg _))
  apply (hasSum_sum (s:=rides N) (fun p _=> ((hs p).hasSum.mul_right (L p)))).congr_fun
  intro i
  by_cases h : (W.row a.2 i).2.walk.length ≤ N
  · have he : (W.row a.2 i).2.walk∈rides N := by simpa [rides] using h
    simp [bundle,ite_mul,he,eq_comm]
  have he : ¬ (W.row a.2 i).2.length ≤ N := by unfold Slot.length; omega
  simp [bundle, Cut.tick,he]

-- ordered derivatives, no commuting inserted directions
lemma left_mul (f : Config G c → ℝ) (x : ℝ) (l : List (Directions G c)) (u : Config G c) : leftDerivs (fun u=>x*f u) l u = x*leftDerivs f l u := by
  induction l generalizing u with | nil => rfl | cons a l ih => rw [leftDerivs]; simp_rw [ih,deriv_const_mul_field]; rfl
lemma left_sum {I : Type*} (f : I → Config G c → ℝ) (l : List (Directions G c)) (u : Config G c) (s : Finset I) (h : ∀ i∈s, WardBin.Lies.Germ l.length (f i) u) : leftDerivs (fun u=> ∑ i∈s, f i u) l u = ∑ i∈s, leftDerivs (f i) l u := by
  induction s using Finset.induction with
  | empty => simp [G07.left_const]
  | insert a t ha ih =>
    have H i (hi : i∈t) := h i (Finset.mem_insert_of_mem hi)
    have ht := ih H
    have he := Multi.Puff.Crest.sum_at (F:=f a) (F':=fun u => ∑ i∈t, f i u) l le_rfl u (Multi.Puff.into _ _ (h a (Finset.mem_insert_self ..))) (Multi.Puff.into _ _ (ContDiffAt.sum H))
    simp_rw [Finset.sum_insert ha]; exact he.trans (congr_arg (leftDerivs (f a) l u + ·) ht)

abbrev Entry (G : Gauge) (f : Side) := Shape.Page G f 2

def segment (W : PathData G) (u : Config G c) := Shape.ell W N (pull s 0 (replica r u))
include hb in
lemma ell_as (x y : Entry G f) (u : Config G c) : segment r s N W u x y = ∑ p∈rides N, (∑' i, bundle N W ((Cut.turn f).symm x.1) ((Cut.turn f).symm y.1) p i) * rail r s x.1.1 x.2 y.2 p u := by
  exact (grouped N hb _ _ (fun p => rail r s x.1.1 x.2 y.2 p u)).tsum_eq

variable (x y : Entry G f) (u : Config G c)
include hb hK
lemma segment_has : WardBin.Lies.Germ k (fun v=>segment r s N W v x y) u := by
  simp_rw [WardBin.Lies.Germ,ell_as r s N hb]; exact ContDiffAt.sum (fun i _=> contDiffAt_const.mul (single_germ k ((rail_pay r s _ _ _ i u hK (Nat.le_add_left 1 k)).order (Nat.zero_le _))))

lemma segment_sum (l : List (Directions G c)) : HasSum (fun i => Cut.tick W N ((Cut.turn f).symm x.1) ((Cut.turn f).symm y.1) i * leftDerivs (rail r s x.1.1 x.2 y.2 (W.row ((Cut.turn f).symm x.1).2 i).2.walk) l u)
    (leftDerivs (fun v=>segment r s N W v x y) l u) := by
  simp_rw [ell_as r s N hb x y]
  rw [left_sum (fun i v=>(∑' z, bundle N W ((Cut.turn f).symm x.1) ((Cut.turn f).symm y.1) i z) * rail r s x.1.1 x.2 y.2 i v) l u _
      (fun i _=> contDiffAt_const.mul (single_germ l.length ((rail_pay r s x.1.1 x.2 y.2 i u hK (Nat.le_add_left 1 k)).order (Nat.zero_le _))))]; simp_rw [left_mul]
  exact grouped N hb _ _ (fun p=>leftDerivs (rail r s _ _ _ p) l u)

-- fixed positive slack σ-w from the actual coefficient receipt
omit hb in
def wagon (G : Gauge) (k q : ℕ) (L : Side) (K a : ℝ) := railPrice G (k+1) K*(1+(L.val:ℝ))^(q*(k+1))*Jets.Weights.spice (2*(k+1)+q*(k+1)) a
omit hb in
lemma segment_bill {q : ℕ} {o : Site f} {t : ℝ} {l : List (Directions G c)} (hl : l.length≤k) (hd : ∀ d∈l, Due r.embed o q t d) (ht : 0≤t) (a b : Cell f) (z z' : G.ColorIndex) (i : ℕ) (hw : 0<w) (hσ : w<σ) : wt w (s.act a.1) (s.act b.1) * (|Cut.tick W N a b i| * ‖leftDerivs (rail r s a.1 z z' (W.row a.2 i).2.walk) l u‖) ≤ E04.rich W σ a.2 i * (wagon G k q r.count K (σ-w)*cap q t o (s.act a.1)^l.length) := by
  have hh := rail_bill r s a.1 z z' (W.row a.2 i).2.walk u hK (hl.trans (Nat.le_succ _)) hd ht
  have he : 0≤cap q t o (s.act a.1) := by unfold cap; positivity
  let a₁ := (1+(r.count.val:ℝ))^(q*(k+1))
  let D := railPrice G (k+1) K*a₁
  have hD := zero_lt_one.trans_le (le_max_left 1 _ : (1:ℝ) ≤ railPrice G (k+1) K)
  have hA : 0 < D := mul_pos hD (by unfold a₁; positivity)
  let T := 2*(k+1)+q*(k+1)
  have hs := Jets.Weights.spicy T (sub_pos.mpr hσ) (x:=0) le_rfl
  have hs' : 0 ≤ Jets.Weights.spice T (σ-w) := zero_le_one.trans (by simpa only [mul_zero,Real.exp_zero,mul_one,add_zero,one_pow] using hs)
  have hW : 0≤wagon G k q r.count K (σ-w) := mul_nonneg hA.le hs'
  unfold Cut.tick E04.rich; split; swap
  · rw [abs_zero,zero_mul,mul_zero]; positivity
  obtain ⟨_,rfl⟩ := ‹_ ∧ _›
  let d := (W.row a.2 i).2
  let x : ℝ := d.length
  have hd : ((1+(d.walk.length:ℝ)))^T ≤ Jets.Weights.spice T (σ-w)*Real.exp ((σ-w)*x) :=
    ((by unfold x Slot.length; push_cast; gcongr; linarith) : (1+(d.walk.length:ℝ))^T ≤ (1+x)^T).trans (Jets.Weights.spicy T (sub_pos.mpr hσ) (Nat.cast_nonneg _))
  unfold wt; rw [separation_signed,mul_left_comm, mul_assoc |(W.row a.2 i).1|]; apply mul_le_mul_of_nonneg_left
  · calc
      _ ≤ Real.exp (w*x)*(D * (1+(d.walk.length:ℝ))^T * cap q t o (s.act a.1)^l.length) := mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left (by unfold x; exact_mod_cast E04.slot_separation d a.1) hw.le)) hh (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (w*x)*(D * (Jets.Weights.spice T (σ-w)*Real.exp ((σ-w)*x))*cap q t o (s.act a.1)^l.length) := by gcongr
      _ = _ := by rw [show σ*(d.length:ℝ)=w*x+(σ-w)*x by unfold x; ring,Real.exp_add]; unfold wagon D a₁ T x; ring
  exact abs_nonneg _
lemma segment_paid {q : ℕ} {t : ℝ} {o : Site f} (hw : 0<w) (hσ : w<σ) (ht : 0≤t) : Sticker r o (fineSite s x) (fineSite s y) w t q k u (fun u=>segment r s N W u x y) (C * wagon G k q r.count K (σ-w)) := by
  refine ⟨segment_has r s N hb hK x y u,fun l hl hd=>?_⟩
  obtain ⟨a,ha⟩ := (Cut.turn f).surjective x.1; obtain ⟨b,hb'⟩ := (Cut.turn f).surjective y.1
  have he := segment_sum r s N hb hK x y u l
  simp_rw [← ha,←hb',Equiv.symm_apply_apply] at he
  have hx (i : ℕ) := segment_bill r s N hK u hl hd ht (W:=W) a b x.2 y.2 i hw hσ
  let E := wt w (fineSite s x) (fineSite s y)
  let M := wagon G k q r.count K (σ-w)* cap q t o (fineSite s x)^l.length
  have H : fineSite s x=s.act a.1 := congr_arg s.act ((congr_arg Prod.fst ha.symm))
  have H' : fineSite s y=s.act b.1 := congr_arg s.act ((congr_arg Prod.fst hb'.symm))
  simp_rw [←H,←H'] at hx
  rw [mul_assoc]
  have hp := (hb.rows a.2).2.1.mul_right M
  calc
    _ ≤ E * ∑' i, ‖Cut.tick W N a b i * leftDerivs (rail r s _ x.2 y.2 (W.row a.2 i).2.walk) l u‖ := mul_le_mul_of_nonneg_left (he.tsum_eq ▸ norm_tsum_le_tsum_norm he.summable.norm) (Green.wt_pos ..).le
    _ ≤ ∑' i, E04.rich W σ a.2 i * M := by rw [←tsum_mul_left]; exact (he.summable.norm.mul_left E).tsum_le_tsum (fun i => by rw [norm_mul]; exact hx i) hp
    _ ≤ C * M := by
      rw [tsum_mul_right]; gcongr; unfold M wagon Jets.Weights.spice cap; have hs := zero_lt_one.trans_le (le_max_left 1 _ : 1≤railPrice G (k+1) K); positivity
      exact (hb.rows _).2.2
omit hb hK in
theorem segment_items (G : Gauge) (k q : ℕ) (L : Side) {σ w C : ℝ} (hw : 0<w) (hσ : w<σ) : ∃ D : ℝ, 0<D ∧ ∀ {c f : Side} (r : Ratio c f), r.count=L → ∀ (o : Site f) (V : Config G c) {p : Clip} {W : PathData G} {Λ t : ℝ}, W.Bounds p σ C Λ → 0 ≤ t → ∀ (s : Signed) (N : ℕ), Items r o (fineSite s) (fineSite s) w t q k V (segment r s N W) D := by
  obtain ⟨K,hK,h⟩ := exp_receipt G (k+1)
  refine ⟨max 1 (C*wagon G k q L K (σ-w)),zero_lt_one.trans_le (le_max_left ..), fun r hr o V p W Λ t hW ht s N i j=>?_⟩
  have hx := segment_paid r s N hW h i j V (o:=o) (q:=q) hw hσ ht
  rw [hr] at hx; exact ⟨hx.good,fun l hl hd=> (hx.paid l hl hd).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by unfold cap; positivity))⟩
end YM.Further.CurvedGaussianJets.ChangeV
