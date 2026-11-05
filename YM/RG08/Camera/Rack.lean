import YM.RG08.Camera.Invoice

/-!
# Lift a real near-chart equivalence of slices (+external locations) to coupled algebra.
Use the SAME internal slot dimension after physical reindexing; input and output external
alphabets may differ to allow arbitrary coarse gauge directions.
-/

noncomputable section
set_option autoImplicit false
namespace YM.RG08.Camera
open Glyph Cloud Room MvPolynomial Finset Filter Function Matrix
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I J A B:Type}[Fintype I][Fintype A][Fintype B]
abbrev Raw (I A:Type):=I ⊕ A

-- Gauze centering in Room & block geometry use `morn`. No Hermitian assumptions beyond price symmetry.
def morn (Γ:Matrix I I ℝ)(h:∀ i j,Γ i j=Γ j i)(A:Type)[Fintype A]: Haze (Raw I A) where
 foam := univ.map (show I↪Raw I A from ⟨.inl,Sum.inl_injective⟩)
 price := Sum.elim (fun i=>Sum.elim (Γ i) (fun _=>0)) (fun _ _=>0)
 flipped i j:=by cases i <;> cases j <;> simp [h]
 dryL i j hh:=by cases i with
    | inl i=>exfalso; simp at hh
    | inr j=>rfl
private lemma listA {Γ:Matrix I I ℝ}{h:∀ i j,Γ i j=Γ j i}{R:Type*}[AddCommMonoid R](f:Raw I A→R): (∑ j∈(morn Γ h A).foam,f j)=∑ j:I,f (.inl j):=by simp [morn]

/-- h transforms unscaled centered coordinates. Last alphabet B purely external depends on A
inputs only (Pace and germ derivatives needed). Internal output has no linear external dependence
at the base point (working CENTERED, pay when proving Lifted). -/
structure Rail (I A B:Type)[Fintype I][Fintype A][Fintype B] where
 h:Strip (Raw I B) (Raw I A)
 L:Matrix I I ℝ
 unitL : IsUnit L
 flat: roll h 0=0
 leading(i:I)(k:I):wedge (Sum.inl k) (h (.inl i)) 0=L i k
 centered(i:I)(k:A):wedge (Sum.inr k) (h (.inl i)) 0=0
 ambient(i:B)(k:I):wedge (Sum.inl k) (h (.inr i))=ᶠ[𝓝 0] (0:Still (Raw I A))
 smooth (i):Pace (h i)
namespace Rail
variable (q:Rail I A B)

def x : Raw I B→Port (Raw I A):=rescaleFields q.h
-- η (on AFTER / Domain of h), b (covariant), L inverse used for fees on each white leg
def b (i:Raw I B):Port (Raw I A):=Sum.elim (fun i:I=>∑ j:I,q.L i j • rod (.inl j)) (fun i:B=>q.x (.inr i)) i
def η (i:Raw I A):Port (Raw I A):=Sum.elim (fun i:I=>∑ j:I,(q.L⁻¹) i j • q.x (.inl j)) (fun a:A=> rod (.inr a)) i
lemma plip (i:Raw I B)(k:Raw I A):pin k (q.x i)=flask (wedge k (q.h i)):=pin_out k q.smooth i
lemma sit {Γ:Matrix I I ℝ}{h:∀ i j,Γ i j=Γ j i}(i:B):Abroad (morn Γ h A).foam (q.x (.inr i)):=by
 intro j hj; rcases j with j|u
 · rw [q.plip,flask_same (q.ambient i j),flask_zero]
 simp [morn] at hj -- false

private lemma seed (i:Raw I B) : tap 0 (q.x i) = ∑ k:Raw I A, wedge k (q.h i) 0 • X k:=by
 rw [x,rescaleFields,look,flute]; unfold print; simp only [Nat.cast_zero,zero_add,inv_one,one_smul]
 apply Finset.sum_congr rfl; intro k _; rw [Algebra.smul_def,mul_comm];rfl
lemma stem (i:I):tap 0 (q.x (.inl i))=∑ k:I,q.L i k • X (.inl k):=by
 rw [seed,Fintype.sum_sum_type];simp_rw [q.leading,q.centered,zero_smul];simp

theorem harbor : Near q.η:=by
 rintro (u|a)
 · change tap 0 (∑ j:I,(q.L⁻¹) u j • q.x (.inl j))=_;unfold tap;rw [map_sum];simp_rw [PowerSeries.coeff_smul,← show ∀ (p:Port (Raw I A)),tap 0 p=PowerSeries.coeff 0 p from fun _=>rfl,stem,Finset.smul_sum,smul_smul];rw [Finset.sum_comm];simp_rw [←Finset.sum_smul,← Matrix.mul_apply,q.L.nonsing_inv_mul (q.L.isUnit_iff_isUnit_det.mp q.unitL),Matrix.one_apply];simp [ite_smul]
 simp [η,tap,rod,liftInn]

theorem fixed {Γ:Matrix I I ℝ}{h:∀ i j,Γ i j=Γ j i}:anchored (morn Γ h A).foam q.η:=by
 rintro (i|a) hi
 · exfalso; simp [morn] at hi
 rfl

theorem assemble (i:Raw I B) : belt q.η (q.b i)=q.x i:=by
 let Ω:=morn (0:Matrix I I ℝ) (by intros;rfl) A
 cases i with
 | inl i=>
    change belt q.η (∑ j:I,q.L i j • rod (Sum.inl j))=_;rw [map_sum];simp_rw [_root_.map_smul,belt_x,η,Sum.elim_inl,Finset.smul_sum,smul_smul];rw [Finset.sum_comm];simp_rw [←Finset.sum_smul,←Matrix.mul_apply,q.L.mul_nonsing_inv (q.L.isUnit_iff_isUnit_det.mp q.unitL),Matrix.one_apply];simp [ite_smul]
 | inr k=> change belt _ (q.x _)=_;rw [abroad_belt (show Abroad Ω.foam _ from q.sit k) (y:=rod) q.fixed,belt_id]

theorem composed (p:Port (Raw I B)):belt q.η (belt q.b p)=belt q.x p:=by
 change ((belt q.η).comp (belt q.b)) p=_; rw [switched,funext q.assemble]

lemma patrol {Γ γ:Matrix I I ℝ}{h:∀ i j,Γ i j=Γ j i}{H:∀ i j,γ i j=γ j i}(hh:q.L*Γ*q.L.transpose=γ):
    ∃ L,Haze.Scout (morn γ H B) (morn Γ h A) q.b L:=by
 let L : Raw I B→Raw I A→ℝ:=Sum.elim (fun i:I=>Sum.elim (q.L i) (fun _=>0)) (fun _ _=>0)
 refine ⟨L,⟨fun i hi=>?_,fun i hi=>?_,fun i k hi hk=>?_⟩⟩
 · rw [listA]; cases i
   · rfl
   exfalso;simp [morn] at hi
 · cases i
   · exfalso;simp [morn] at hi
   apply q.sit
 simp_rw [listA];rcases i with (i|i); rotate_left
 · exfalso;simp [morn] at hi
 rcases k with k|k;rotate_left
 · exfalso;simp [morn] at hk
 change ∑ a:I,∑ b:I,Γ a b*q.L i a*q.L k b=γ i k
 conv_rhs=>rw [← hh,mul_apply]
 simp_rw [mul_apply,transpose_apply,Finset.sum_mul]
 rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring

/- jacBlock h normalized by detL⁻¹ -/
def jac (z:Cellar (Raw I A)):ℝ:=(q.L⁻¹ * Matrix.of (fun i j : I=> wedge (Sum.inl j) (q.h (.inl i)) z)).det
lemma jac_flat : q.jac 0=1:=by
 unfold jac;simp_rw [q.leading];change (q.L⁻¹*q.L).det=_;rw [Matrix.nonsing_inv_mul _ (q.L.isUnit_iff_isUnit_det.mp q.unitL),Matrix.det_one] -- Matrix.of _ defeq

lemma jac_pace : Pace q.jac:=by
 unfold jac; simp_rw [Matrix.det_apply']
 apply ContDiffAt.sum;intro b _;apply ContDiffAt.mul contDiffAt_const
 apply contDiffAt_prod; intro i _; simp only [Matrix.mul_apply,Matrix.of_apply]
 exact ContDiffAt.sum (fun k _=> ContDiffAt.mul contDiffAt_const (Pace.wedge _ (q.smooth _)))

def brush : Matrix I I (Port (Raw I A)):=Matrix.of fun (i j:I)=>∑ k:I,(q.L⁻¹) i k • flask (wedge (Sum.inl j) (q.h (.inl k)))
lemma jac_gloss : flask q.jac=q.brush.det:=by
 let M (z:Cellar (Raw I A)):= q.L⁻¹*Matrix.of (fun i j:I=>wedge (Sum.inl j) (q.h (.inl i)) z)
 have he(i j:I):(fun z=>M z i j)=∑ k:I,(q.L⁻¹) i k • wedge (Sum.inl j) (q.h (.inl k)):=by funext z;unfold M;rw [Matrix.mul_apply,Finset.sum_apply];rfl
 have hp(i j k:I): Pace ((q.L⁻¹) i k • wedge (Sum.inl j) (q.h (.inl k))) := (Pace.wedge _ (q.smooth _)).const_smul ((q.L⁻¹) i k)
 change flask (fun z=>Matrix.det (M z))=_;rw [flask_det (by intro i j; rw [he];simpa only [←Finset.sum_apply] using (ContDiffAt.sum (s:=univ) (f:=fun k:I=> (q.L⁻¹) i k • wedge (Sum.inl j) (q.h (.inl k))) (fun k _=>hp i j k)))]; congr 1;ext i j :1; simp only [Matrix.of_apply,he,brush,slurry _ _ (fun k _=>hp i j k),flask_scale (Pace.wedge _ (q.smooth _))]
 -- named args etc.
theorem fees : flask q.jac=(gate q.η).det:=by
 let D : Matrix I A (Port (Raw I A)):=Matrix.of (fun i j=>pin (Sum.inr j) (q.η (.inl i)))
 let C : Matrix A A (Port (Raw I A)):=1
 -- align instances by applying real det_fromblocks & gate_eq rewriting at identified instances
 have he: gate q.η= Matrix.fromBlocks q.brush D 0 C:=by
    ext i j :1
    cases i <;> cases j
    · rename_i i j;change pin (Sum.inl j) (∑ k:I,(q.L⁻¹) i k • q.x (.inl k))=_;rw [map_sum];simp_rw [Derivation.map_smul,q.plip];rfl
    · rfl
    · rename_i i j;change pin (.inl j) (rod (I:=Raw I A) (Sum.inr i))=0;simp [pins]
    rename_i i j;change pin (Sum.inr j : Raw I A) (rod (Sum.inr i))=C i j;simp [C,pins,eq_comm,Matrix.one_apply]
 rw [q.jac_gloss,he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one] -- C

end Rail
end YM.RG08.Camera
