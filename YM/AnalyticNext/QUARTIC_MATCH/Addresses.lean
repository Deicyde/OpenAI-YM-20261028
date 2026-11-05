import Mathlib.Analysis.Complex.Schwarz
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Per
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Post
import YM.AnalyticNext.QUARTIC_MATCH.Multiples
import YM.Org.Theatre

/-!
# Charge every actual placement. Relative addresses and orientations
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Lattice RG Precision Bid Function Matrix Wilson Exterior Filter Laurent Tensor Joint BoxChain
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

namespace Mail
variable {G : Gauge} {c : Side} {n : ℕ}

abbrev Address (n : ℕ) := (Fin (n+1) → TypeFace 2) × (Fin n→Cover)

-- n displacement slots first-anchored. Not truncated when periodizing.
abbrev rootArray (G : Gauge) (n : ℕ) := ArrayC (Fin (n+1)) ℤ (ColorPart G (n+1))
def offset (v : Address n) : Fin (n+1)→Cover := Fin.cons 0 v.2
def cells (v : Address n) : Fin (n+1)→Cell ℤ := fun i => (offset v i,(v.1 i).val)



def place (b : Site c) (a : Address n) : Fin (n+1)→Cell (Per c) := move b ∘ tor c ∘ cells a
lemma place_base (b : Site c) (a : Address n) : (place b a 0).1=b := by simp [place,move,offset,cells,tor]

-- bijection of relative keys at fixed periodic positions
section fibers
variable (X : Fin (n+1) → Cell (Per c))
private abbrev base := (X 0).1

def package (v : sheets c (0:Fin (n+1))) (h : ∀ i, (X i).2.card=2) : Address n := (
    fun i => ⟨_,h i⟩, fun i => (lift (X i.succ).1 + v.val i.succ) - lift (base X))
lemma embody (v : sheets c (0:Fin (n+1))) (h : ∀ i, (X i).2.card=2) :
    move (lift (base X)) ∘ cells (package X v h)=sway v.val (rise c ∘ X) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i
  · simp [package,cells,sway,offset,move,rise,sheet_here,base]
  simp [package,cells,sway,offset,move,rise]
lemma lands (v : sheets c (0:Fin (n+1))) (h : ∀ i, (X i).2.card=2) :
    place (base X) (package X v h)=X := by
  have he := embody X v h; funext i
  calc
    _ = tor c ((move (lift (base X)) ∘ cells (package X v h)) i) := by simp only [place, tor_move,Function.comp_apply,wrap_lift]
    _ = _ := by rw [he]; simp only [Function.comp_apply,sway,tor_move,sheet_wrap,to_ground]; simp [move]

def unpack (v : {v : Address n // place (base X) v=X}) : sheets c (0:Fin (n+1)) := by
  let w i := offset v.val i + lift (base X)-lift (X i).1
  refine ⟨w,fun j => ?_,?_⟩
  · have he := congr_arg Prod.fst (congr_fun v.property j)
    change wrap c (offset v.val j) + _ = _ at he
    unfold w; rw [map_sub,map_add,wrap_lift,wrap_lift,he,sub_self]
  simp [w,base,offset]

lemma unpacked (h : ∀ i, (X i).2.card=2) (v : {v : Address n // place (base X) v=X}) : package X (unpack X v) h=v.val := by
  apply Prod.ext
  · refine funext fun i => ?_; apply Subtype.ext; exact congr_arg Prod.snd (congr_fun v.property i).symm
  funext i; change lift (X i.succ).1+(_+ _-lift (X i.succ).1)-lift (base X)=_
  simp only [offset,Fin.cons_succ]; abel

def line (h : ∀ i, (X i).2.card=2) : ↥(sheets c (0:Fin (n+1))) ≃ {v : Address n // place (base X) v=X} where
  toFun v := ⟨package X v h,lands X v h⟩
  invFun := unpack X
  left_inv v := by
    apply Subtype.ext
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · exact (sheet_here ..).trans (sheet_here c _ v).symm
    change offset (package X v h) j.succ + lift (base X)-lift (X j.succ).1 = _
    simp [offset,package]
  right_inv v := Subtype.ext (unpacked X h v)

/-- Compute a tensor entry by the actual address sum. -/
lemma arrives (F : rootArray G n) (hf : Cohere F) (h : ∀ i, Rank F i 2) : scene c 0 F X =
    ∑' v : Address n, if place (base X) v=X then F (cells v) else 0 := by
  classical
  by_cases hv : ∀ i, (X i).2.card=2
  · let S := {v : Address n|place (base X) v=X}
    unfold scene echo
    trans ∑' z : ↥S,F (cells z.val)
    · have he := Equiv.tsum_eq (line X hv) fun z => F (cells z.val)
      apply Eq.trans ?_ he
      refine tsum_congr fun i => ?_
      rw [← embody X i hv, hf]; rfl
    have hu := _root_.tsum_subtype S (fun z => F (cells z))
    apply hu.trans; apply tsum_congr; intro i; simp [Set.indicator,S]
  push Not at hv; obtain ⟨i,hi⟩ := hv
  have he (w : sheets c (0:Fin (n+1))) : F (sway w.val (rise c ∘ X))=0 := h i _ hi
  have ha (v : Address n) : place (base X) v ≠ X := fun hz => hi ((congr_arg (fun x : Cell _ => x.2.card) (congr_fun hz i)).symm.trans (v.1 i).property)
  simp [scene,echo,he,ha]
end fibers

lemma net (v : Address n) : loads (fun i => (cells v i).1-(cells v 0).1)=loads v.2 := by
  simp [loads,cells,offset,Fin.sum_univ_succ,Laurent.size]

-- Budget over positions AND all faces, ready for multiplying by absolute coefficients
lemma supply {σ : ℝ} (hp : 0<σ) (n : ℕ) : SumBudget (fun v : Address n => Real.exp (-σ * loads v.2))
    (Fintype.card (Fin (n+1) → TypeFace 2)*((2*((1+σ)/σ))^(Fintype.card (Fin n × Axis)))) := by
  have he := pays_all (I:=Fin n) hp
  let f (v : Address n) := Real.exp (-σ * loads v.2)
  have hp (a b) : 0≤f (a,b) := he.1 _
  have hf : Summable f := (summable_prod_of_nonneg (fun ⟨_,_⟩ => hp _ _)).2
    ⟨fun _ => he.2.1,.of_finite⟩
  refine ⟨fun _ => (Real.exp_pos _).le,hf,?_⟩
  rw [hf.tsum_prod,tsum_fintype]; unfold f
  dsimp only; rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_left he.2.2 (by positivity)

variable {F : rootArray G n} {σ C : ℝ} [ne : NeZero n]
-- n positive in classical use
omit ne in
lemma ink_abs (h : Pricing F σ C) : Summable fun i : Address n => ‖F (cells i)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => ?_) ((supply (positive_rate h.rate (0:Fin (n+1))) n).2.1.mul_left C)
  exact le_of_le_of_eq (pricing_anchor h (0:Fin (n+1)) (cells i)) (by rw [net])

omit ne in
lemma ink_delivery (hp : Pricing F σ C) (h : ∀ i, Rank F i 2) (U : Fin (n+1)→ Ink G c) :
    post (scene c 0 F) U=∑ x : Site c, ∑' j : Address n,
      (F (cells j)).val (fun i => U i (place x j i)) := by
  classical
  let A x (j : Address n) := (F (cells j)).val (fun i => U i (place x j i))
  let Q (X : Fin (n+1)→Cell (Per c)) x (j : Address n) : ColorPart G (n+1) :=
    if place x j=X then F (cells j) else 0
  have he (X x) : Summable (Q X x) := by
    refine Summable.of_norm_bounded (ink_abs hp) (fun i => ?_)
    unfold Q; split; · exact le_rfl
    rw [norm_zero]; exact norm_nonneg _
  let L (X : Fin (n+1)→Cell (Per c)) : ColorPart G (n+1) →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ (fun i => U i (X i))) ∘L (eligible G (n+1)).subtypeL
  have hx (X : Fin (n+1)→Cell (Per c)) : scene c 0 F X = ∑ x : Site c, ∑' j, Q X x j := by
    rw [Finset.sum_eq_single ((X 0).1)]; · exact arrives X F hp.same h
    · intro b _ hb
      have hd (i) : Q X b i=0 := if_neg fun h => hb ((place_base b i).symm.trans (congr_arg (fun x : Fin (n+1) → Cell _ => (x 0).1) h))
      simp [hd]
    simp
  unfold post
  change ∑ X, L X (scene c 0 F X)=∑ x : Site c,∑' j,A x j
  simp_rw [hx,map_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _
  simp_rw [ (L _).map_tsum (he _ _)]; rw [← Summable.tsum_finsetSum]
  · apply tsum_congr; intro j
    rw [Finset.sum_eq_single (place x j)]
    · rw [show Q (place x j) x j=F (cells j) from if_pos rfl]; rfl
    · intro b _ h; rw [show Q b x j=0 from if_neg (Ne.symm h),map_zero]
    simp
  exact fun i _ => (he i x).mapL (L i)
end Mail
end YM.AnalyticNext.QuarticMatch
