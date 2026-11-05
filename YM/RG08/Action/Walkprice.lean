import YM.RG08.Action.Accessories
/-! # Exact one step path price. Generate fine stencil AFTER input
packing, weight linear in relative distances. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Staffer
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect Conductor Bloch UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m c f : Side}
variable {p r : ℕ} {F : Pot G p} {u C w : ℝ}
local notation "L" => Fin r → Lacing G p
local notation "B" => Beads (Loc G 1) p

def icing (u : Fin p → Loc G 1) (v : L) := Tensor.coeff (minted u) r 0 (fun i=> Pi.single (v i) 1)
def sweets (p : B) (v : L) := confection p ∘ v
def silkSale (G : Gauge) (p r : ℕ) := ∑ u: Fin p→ Loc G 1, ∑ v: Fin r→ Lacing G p, ‖icing u v‖
lemma ice_fee (u : Fin p → Loc G 1) : ∑ v:L, ‖icing u v‖≤ silkSale G p r := single_le_sum (fun _ _=>sum_nonneg fun _ _=> norm_nonneg _) (mem_univ _)
lemma silkSale_pos (G : Gauge)(p r : ℕ) : 0≤ silkSale G p r := sum_nonneg (fun _ _=> sum_nonneg (fun _ _=> norm_nonneg _))
private lemma liftMari (x : Tensor.T (Corn (Lacing G p)) ℝ r)(v : Fin r→ Corn (Lacing G p)) :
    x v=∑ t:L,(∏ i,v i (t i))*x (fun i=> Pi.single (t i) 1) := by
  have h := expand_coord x.toMultilinearMap v; rw [recording_apply] at h; exact h.symm

lemma ice_unit (u : B)(z : Site m)(x : PAC (Candles G) m) :
    ink (fun t:ℝ=> rosary (r:=p) (fun _=> dragged G m (t • x)) z u) r=
      ∑ v:L,icing (Prod.snd ∘ u) v * rosary (fun _=>x) z (sweets u v) := by
  simp_rw [← studs_read,map_smul]
  rw [pulse_ray _ r ((minted_art _).contDiffAt.of_le le_top),jet_coefficient,Tensor.diagonal, liftMari]; exact sum_congr rfl fun j _=>mul_comm ..
lemma silk_thin (u : B)(t : L) : girth (sweets u t)≤ r*(girth u+1) :=
  (sum_le_sum (s:=univ) (f:=fun i:Fin r=> size (sweets u t i).1) (g:=fun _=>girth u+1) (fun _ _ => studs_len ..)).trans_eq (by simp)
def aglow (F : Pot G p) (u : B × (L)) := F u.1 * icing (Prod.snd ∘ u.1) u.2
def cropWax (F : Pot G p) (r : ℕ) := pool (aglow (r:=r) F) (fun z=> sweets z.1 z.2)
private lemma silkLens (hF : Glow F w C) (h : 0 ≤ u) (he : r*u ≤ w) :
    Charge (fun i=> ling u (sweets (G:=G) (p:=p) (r:=r) i.1 i.2)) (aglow F) ((Real.exp (r*u)* silkSale G p r)*C) := by
  apply leads_cost (mul_nonneg (Real.exp_pos _).le (silkSale_pos ..)) hF -- family inferred
  intro i
  refine budget_finite (fun j=>mul_nonneg (ling_pos _ _).le (norm_nonneg _)) ?_
  have hv : ∀ (j : L), ling u (sweets i j) ≤ Real.exp (r*u)*ling w i := by
    intro j; unfold ling; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have hV : u*((girth (sweets i j)):ℝ) ≤ u*(r*(girth i+1:ℕ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast silk_thin i j) h
    apply hV.trans; push_cast; nlinarith only [mul_le_mul_of_nonneg_right he (show 0≤(girth i:ℝ) from Nat.cast_nonneg _)]
  refine le_trans (b:= (Real.exp (r*u)*ling w i)*∑ j:L, ‖icing (Prod.snd ∘ i) j‖) ?_ ?_
  · rw [Finset.mul_sum]; exact sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _))
  rw [mul_right_comm (Real.exp _) (silkSale ..)]; exact mul_le_mul_of_nonneg_left (ice_fee ..) (mul_pos (Real.exp_pos _) (ling_pos _ _)).le
lemma silkFees (hF : Glow F w C) (h : 0≤u) (he : r*u ≤ w) : Glow (cropWax F r) u ((Real.exp (r*u)*silkSale G p r)*C) := by
    unfold cropWax; exact Charge.poolage (fun z:B × (L)=>sweets z.1 z.2) (ling_one h) (silkLens hF h he)
private lemma kerry (hF : Summable F) : Summable (aglow F (r:=r)) := by
  have hp: Glow F 0 (∑' i,‖F i‖) := by unfold Glow ling Charge; simp only [zero_mul,Real.exp_zero,one_mul]; exact ⟨fun i=>norm_nonneg _,hF.norm,le_rfl⟩
  exact (silkLens hp (show (0:ℝ)≤0 from le_rfl) (show (r:ℝ)*0≤0 by simp)).summable (fun i=> ling_one le_rfl _)
lemma silkSum (hf : Summable F) : Summable (cropWax F r) := ((kerry hf).hasSum.tsum_fiberwise _).summable

private lemma tally (hf : Summable F) (x : PAC (Candles G) m) (z : Site m) (r : ℕ) :
    let v (t:ℝ):= dragged G m (t•x)
    ink (fun t=> stitch F m z (fun _:Fin p=>v t)) r = ∑' u:B,F u*ink (fun t=>rosary (fun _=> v t) z u) r := by
  intro v
  let T := Fin p→ Co m (Loc G 1); let P: B→ T := silks z; let m' (p:T) (t:ℝ):= ∏ j, v t (p j)
  have hv : ContDiffAt ℝ ∞ v 0 := (((zero_smul ℝ x).symm ▸ (show ContDiffAt ℝ ∞ (dragged G m) 0 from dragged_analytic.contDiffAt.of_le le_top))|>.comp (f:=fun t:ℝ=> t•x) _ (contDiffAt_id.smul contDiffAt_const)) -- zero drag point
  have hp t : ContDiffAt ℝ ∞ (m' t) 0 := contDiffAt_prod (fun i _=> contDiffAt_pi.mp hv _)
  unfold stitch; change ink (fun t=>recording _ _) r=_ -- might stuck
  simp_rw [recording_apply];
  let V b:= m' b * fun _=> pool F P b
  change ink (fun t=>∑ b:T,V b t) r=_
  rw [ink_list univ V (fun i _=> (hp i).mul contDiffAt_const)];
  have he := pool_total (f:=F) (fun p=> ink (m' p) r) P hf (fun i=> single_le_sum (f:=fun t=> ‖ink (m' t) r‖) (fun _ _=>norm_nonneg _) (mem_univ i));
  rw [tsum_fintype] at he
  refine Eq.trans (sum_congr rfl (fun i _=>?_)) he
  rw [show V i=(pool F P i) • m' i from funext fun t=>mul_comm ..,ink_c _ (hp i)]; rfl
lemma silkOpus (hf : Summable F) (x : PAC (Candles G) m) : ink (fun t:ℝ=> stanza F m (dragged G m (t•x))) r= stanza (cropWax F r) m x := by
  let v (t:ℝ):= dragged G m (t•x)
  unfold stanza Tensor.diagonal cropWax; rw [recital_pool _ (kerry hf)];
  have he : (fun t:ℝ=> recital F m (fun _=>v t))=(fun t=> ∑ z,stitch F m z (fun _=>v t)) := by funext t; unfold recital; rw [_root_.sum_apply]
  rw [show (fun t:ℝ=> recital F m (fun _=> dragged G m (t•x)))=_ from he]
  have hv : ContDiffAt ℝ ∞ v 0 := (((zero_smul ℝ x).symm ▸ (show ContDiffAt ℝ ∞ (dragged G m) 0 from dragged_analytic.contDiffAt.of_le le_top))|>.comp (f:=fun t:ℝ=> t•x) _ (contDiffAt_id.smul contDiffAt_const))
  rw [ink_list univ (fun z t=>stitch F m z (fun _=> v t)) (fun i _=> ((Tensor.diag_smooth (stitch F m i) ∞).contDiffAt.comp _ hv))]
  apply sum_congr rfl; intro z _; rw [show ink _ r=_ from tally hf x z r]; rw [Summable.tsum_prod' (f:=fun i:B × (L)=> aglow F i*rosary (fun _=>x) z (sweets i.1 i.2))]
  · refine tsum_congr fun i=> ?_; rw [ice_unit,tsum_fintype, Finset.mul_sum]; exact sum_congr rfl (fun j _=> (mul_assoc ..).symm)
  · exact sum_bounded (kerry hf) (fun i=> rosary_bill ..)
  · exact fun i=> Summable.of_finite

-- companion certificate for single centered terms, for source version
lemma tallyOpus (hf : Summable F) (x : PAC (Candles G) m) (z:Site m) : ink (fun t:ℝ=> (Tensor.diagonal (stitch F m z)) (dragged G m (t•x))) r= Tensor.diagonal (stitch (cropWax F r) m z) x := by
  unfold Tensor.diagonal; rw [show ink _ r=_ from tally hf x z r]; unfold cropWax; let s : B×(L)→ ℝ:= fun i=> aglow F i*rosary (fun _=>x) z (sweets i.1 i.2); rw [stitch_apply (show Summable (pool (aglow (r:=r) F) (fun z=>sweets z.1 z.2)) from silkSum hf) _ z, pool_total (rosary (fun _:Fin r=>x) z) (fun i:B × (L)=> sweets i.1 i.2) (kerry hf) (rosary_bill (fun _=>x) z), (show Summable s from sum_bounded (kerry hf) (fun i=> rosary_bill ..)).tsum_prod]
  refine tsum_congr fun i=>?_ ; rw [ice_unit,tsum_fintype,Finset.mul_sum]; exact sum_congr rfl fun j _=> (mul_assoc ..).symm
lemma silkPens (hf : Summable F) : Summable (aglow F (r:=r)) := kerry hf
lemma silkBone (hF : Glow F w C) (h : 0≤u)(hp : r*u ≤ w) : Charge (fun i=> ling u (sweets (G:=G) (p:=p) (r:=r) i.1 i.2)) (aglow F) ((Real.exp (r*u)* silkSale G p r)*C) := silkLens hF h hp
end YM.RG08.Staffer
