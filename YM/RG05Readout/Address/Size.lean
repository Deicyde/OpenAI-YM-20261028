import YM.RG05Readout.Address.Saved
/-!
# Common head and cone coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G: Gauge}{C: Family G}{d:ℕ}
abbrev Mark (C:Family G)(d:ℕ):= (i:Letter d) × (C.labels.level (kept i)).Index
abbrev weights {d:ℕ} (j:Mark C d):=depth j.1 + ((C.labels.level (kept j.1)).grades j.2).1
lemma capped (i:Mark C d): weights i ≤ d:= by
    have h:depth i.1 ≤ d:= Nat.le_of_lt_succ i.1.1.isLt
    exact (Nat.add_le_add_left ((C.labels.level (kept i.1)).bound i.2) _).trans_eq (Nat.add_sub_of_le h)

def val (f:Palette C d)(i:Mark C d):ℂ:= f i.1 i.2
def size (f:Palette C d):ℝ:=∑ i:Mark C d, ‖val f i‖
lemma bill_group (f:Palette C d):size f=∑ i:Letter d,(C.labels.level (kept i)).coeffSize (f i):=by
   rw [size,Fintype.sum_sigma];rfl
lemma size_zero: size (0:Palette C d)=0:=by simp [size,val]
lemma size_ge (f:Palette C d):0≤ size f:= Finset.sum_nonneg (fun _ _=>norm_nonneg _)
lemma each_price (f:Palette C d)(i:Mark C d):‖val f i‖ ≤ size f:= Finset.single_le_sum (f:=fun j=> ‖val f j‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ i)
lemma size_add (f g:Palette C d):size (f+g)≤ size f+size g:=by simp only [bill_group,← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=> Size.add ..
lemma size_sum {ι:Type*}(p:Finset ι)(f:ι→Palette C d):size (∑ i∈p,f i) ≤ ∑ i∈p,size (f i):=by
   induction p using Finset.induction_on with
   | empty => simp [size_zero]
   | @insert i p hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (size_add ..).trans (add_le_add le_rfl ih)
lemma size_smul (c:ℂ)(f:Palette C d): size (c • f)=‖c‖*size f:=by simp only [bill_group,Finset.mul_sum,Pi.smul_apply,Size.smul]
lemma size_neg (f:Palette C d):size (-f)=size f:= by rw [← neg_one_smul ℂ f,size_smul,norm_neg,norm_one,one_mul]
lemma size_norm (f:Palette C d): ‖f‖ ≤ size f:=
  (pi_norm_le_iff_of_nonneg (size_ge _)).mpr (fun i=> (pi_norm_le_iff_of_nonneg (size_ge _)).mpr (fun j=>each_price f ⟨i,j⟩))

open Trace.Physical
variable (d) (S:Family G) {n:Side}{R:Rep G n}{o:Site n}
def wrap_price :ℝ:=1+ ∑ i:Letter d,((((S.labels.level (kept i)).extra+1:ℕ):ℝ)*((Trace.Physical.Germ.germ_close (S.labels.level (kept i)) S.params).choose))
lemma price_nn:1 ≤ wrap_price d S:= le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> mul_nonneg (by positivity) ((Trace.Physical.Germ.germ_close ..).choose_spec.1.le))
theorem wraps_paid {P:Tape G n}{v w:Palette S d} {u t:ℝ}(h:Printed S d R o t P v w u)(hd:d ≤ R.p.order)(he:d≤ R.p.power): size (w-v)≤ wrap_price d S * Trace.Physical.Germ.wraps R.p n * u:=by
     rcases h with @⟨L,F,v,b,H,h,hp,rfl,rfl,rfl,hu⟩
     let f(i:Letter d):=(((S.labels.level (kept i)).extra+1:ℕ):ℝ)
     let g(i:Letter d):=((Trace.Physical.Germ.germ_close (S.labels.level (kept i)) S.params).choose)
     let y:=Trace.Physical.Germ.wraps R.p n; have hg(i:Letter d):0≤g i :=(Trace.Physical.Germ.germ_close ..).choose_spec.1.le
     have ht:0 ≤ wrap_price d S:=zero_le_one.trans (price_nn ..); have hδ: 0≤ y:=(Real.exp_pos _).le; let w:=wrap_price d S
     rw [bill_group]; apply le_trans (b:=w*y*∑ i,v i); rotate_left
     · exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right H.nonneg).trans hu) (mul_nonneg ht hδ)
     rw [Finset.mul_sum]; apply Finset.sum_le_sum
     intro i _; let v':=(L i); let d':=kept i
     change (S.labels.level (kept i)).coeffSize _ ≤ w*y*v i
     have hv : f i*g i ≤ w:= (Finset.single_le_sum (f:=fun i=>f i*g i) (fun i _=> mul_nonneg (by dsimp [f]; positivity) (hg i)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
     have hζ:= (Trace.Physical.Germ.germ_close ..).choose_spec.2 _ (L i) (h i) (hp i) ((Nat.sub_le ..).trans hd) ((Nat.sub_le ..).trans he)
     refine (size_le_norm _ _).trans ((mul_le_mul_of_nonneg_left hζ (show 0≤f i from by unfold f; positivity)).trans ?_)
     change f i * (g i*y*v i) ≤ _; rw [← mul_assoc, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv hδ) (rem_nonneg (hp i))

def amplify (x:Side) : Palette S d→ₗ[ℂ]Palette S d where
    toFun v:=fun i=>vowel (S.labels.level (kept i)) x (v i)
    map_add' v w:=by funext i j; exact mul_add ..
    map_smul' v w:=by funext i j; refine mul_left_comm ..
variable {d S}
open Offsets
noncomputable def clear (C:Family G)(d n:ℕ):Palette C d→ₗ[ℂ]Palette C d where
   toFun x:= fun i j => if weights (Sigma.mk i j:Mark C d)≤n then x i j else 0
   map_add' x y:=by funext i j; dsimp; split<;> simp
   map_smul' x y:=by funext i j; dsimp; split<;> simp
lemma size_cap (j:ℕ)(x:Palette C d): size (clear C d j x) ≤ size x:=by
    exact Finset.sum_le_sum (fun i _=> show ‖if weights i ≤ j then val x i else 0‖ ≤ ‖val x i‖ from by split <;> simp)
end YM.RG05Readout.Address
