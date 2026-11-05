import YM.Planned.PRIMARY_INTEGRAL_295.Floor
/-!
# A localized Hub covers the principal patch receipt on C columns

Physical interpretation attested by Loom.WindowProof later. Keep rectangle
of ALL columns needed for I. Require finite post size actually earned before-L
consumer scheduling post-index prices including varying H.C,I. B under f plot.
Don't derive general C on original period, sufficient for Lxe singleton.
Positions embedding unique, never identify duplicate midpoint/color elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Glints
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Tropics Cedar Precision Exterior Tree Streets Porous Carrier Bloch
open Progress.StationaryScenes.Green Push.Uniform Matrix Floor
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F ι κ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n k : ℕ} {C M σ α u s : ℝ} {f : Side} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

structure Windows (e : κ↪ι) where
    W : κ→Finset ι
    holds : ∀ i,e i∈W i
namespace Windows
variable {e : κ↪ι} (K:Windows e)
-- eventual Charts points on one stable W per marginal click.
def anchor (i:κ) : K.W i:= ⟨e i,K.holds i⟩

def chamber (i:κ) (A:Matrix ι ι ℝ) : Matrix (K.W i) (K.W i) ℝ:= A.submatrix (Subtype.val :(K.W i)→ι) Subtype.val
def reed (A:Matrix ι ι ℝ) (i:κ) (j:ι) := if h:j∈K.W i then (K.chamber i A)⁻¹ ⟨j,h⟩ (K.anchor i) else 0

def coin (A:Matrix ι ι ℝ) := Matrix.of fun i j : κ=> (1/2:ℝ) * (K.reed A i (e j) + K.reed A j (e i))
omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma coin_symmetric (A:Matrix ι ι ℝ) :(K.coin A).IsHermitian:=by
  ext i j; unfold coin; simp [conjTranspose_apply,add_comm]
omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma reed_inside (A:Matrix ι ι ℝ) (i:κ) (j:K.W i) : K.reed A i j.val=(K.chamber i A)⁻¹ j (K.anchor i):=dif_pos j.property
omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma reed_outside (A:Matrix ι ι ℝ) (i:κ) (j:ι) (h:j∉K.W i) : K.reed A i j=0:=dif_neg h

-- radius measured d_L from true map l in output coarse modulo; core ancestry includes proof κ all queried. mirror actual h.
structure Glaze (h:Aim) (A:E→Matrix ι ι ℝ) (l:ι→ Site f) (k:ℕ) (u:ℝ) (r:ℕ) : Prop where
    price : 1≤u
    camp : h.Camp (A 0) l
    core : Vault h l A k u
    heat : h.cap ≤ u
    mirror : ∀ᶠ y in 𝓝 (0:E), (A y).IsHermitian
    tops : (Fintype.card ι:ℝ) ≤ u
    stars : ∀ (i:κ) (j:ι), j∉K.W i → r ≤ separation (l (e i)) (l j)

namespace Glaze
variable {h:Aim} {A:E→Matrix ι ι ℝ} {r:ℕ} {l:ι→Site f} (H: K.Glaze h A l k u r)
include H
omit [DecidableEq κ] [Fintype κ] in
lemma attends (i:κ) :
    let f':=K.chamber i (A 0); let l':=(l ∘ Subtype.val:(K.W i)→ Site f)
    f'*f'⁻¹=1 ∧ f'⁻¹*f'=1 ∧ (∀ a b:(K.W i), ‖(f'⁻¹) a b‖ ≤ h.cap*h.Dust (l' a) (l' b)) ∧
       Vault h l' (fun y=>(K.chamber i (A y))⁻¹) k (willow u k) := by
   intro f' l'; let e':=(Function.Embedding.subtype (fun z:ι=> z∈K.W i))
   have he:= Aim.Camp.take h H.camp e'; obtain ⟨hh,hq,hg⟩:= Aim.Camp.cost h he
   have hd := ribbons h l' he H.heat H.price (A:=fun y=>K.chamber i (A y))
     (fun i j=>H.core i.val j.val) ((Nat.cast_le.mpr (Fintype.card_le_of_embedding e')).trans H.tops)
   exact ⟨hh,hq,hg,hd⟩

omit [DecidableEq κ] [Fintype κ] in
lemma ticking (i:κ) (j:ι) : ‖K.reed (A 0) i j‖ ≤ u*h.Dust (l (e i)) (l j) ∧
      Ember k (fun x=>K.reed (A x) i j) (willow u k*h.Dust (l (e i)) (l j)) := by
   have hp:=H.price; have he:=(h.dust_pos (l (e i)) (l j)).le; have hv:=will_le hp k
   by_cases hr:j∈K.W i
   · let k':K.W i:=⟨_,hr⟩; obtain ⟨-, -,hs,hq⟩:= H.attends K i
     have ht:=hs k' (K.anchor i); have hy:=hq k' (K.anchor i)
     rw [show h.Dust _ (l j)=h.Dust (l j) (l (e i)) from decay_comm ..] at he ⊢
     simp_rw [show j=k'.val from rfl,K.reed_inside]; exact ⟨ht.trans (mul_le_mul_of_nonneg_right H.heat he),hy⟩
   simp_rw [K.reed_outside _ i j hr]; refine ⟨by rw [norm_zero]; positivity,Ember.weakening (Ember.neutral k) ?_⟩; exact mul_nonneg ((zero_le_one.trans hp).trans hv) he

omit [DecidableEq κ] [Fintype κ] in
lemma licked (i j:κ):Ember k (fun x=> K.coin (A x) i j) (willow u k):= by
   let v:= willow u k; have he := will_le H.price k; have hv : 1≤v:= H.price.trans he
   have hf (i j:κ):= Ember.weakening (H.ticking K i (e j)).2 (mul_le_of_le_one_right (zero_le_one.trans hv) (h.dust_le ..))
   have hg:= Ember.scaled (Ember.join (hf i j) (hf j i)) (1/2:ℝ)
   rw [Real.norm_of_nonneg (by positivity : 0≤(1/2:ℝ)), show 1/2*(v+v)=v by ring] at hg; exact hg
end Glaze

def mist (h:Aim) (r:ℕ) := Real.exp (-h.starry*r)
lemma mist_pos (h:Aim) (r:ℕ):0<mist h r:= Real.exp_pos _
lemma departed (h:Aim) {i j : Site f} {r:ℕ} (he:r≤separation i j) : h.Dust i j ≤ mist h r :=
   Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr he) (neg_nonpos.mpr h.starry_pos.le))

section Leave
variable {h:Aim} {A:E→Matrix ι ι ℝ} {r:ℕ} {l:ι→ Site f} (H : K.Glaze h A l k u r)

omit [DecidableEq κ] [Fintype κ] in
private lemma stem (A:Matrix ι ι ℝ) (i:κ) (hi : K.chamber i A*(K.chamber i A)⁻¹=1) (j:ι) (hh:j∈K.W i):
      (A.mulVec (K.reed A i)) j = (1:Matrix ι ι ℝ) j (e i):= by
   let W:=K.W i; let j':K.W i:=⟨j,hh⟩
   calc
    _ = ∑ k∈W, A j k*K.reed A i k := by
      unfold Matrix.mulVec dotProduct; apply Eq.symm (Finset.sum_subset (Finset.subset_univ _) ?_); intro i _ hi; rw [K.reed_outside ..,mul_zero]; exact hi
    _ = (1:Matrix W W ℝ) j' (K.anchor i) := by
      rw [←hi,Matrix.mul_apply,← Finset.sum_coe_sort W]; apply Finset.sum_congr rfl
      intro w _; rw [K.reed_inside A i w]; rfl
    _ = _ := by by_cases h:j=e i <;> simp [Matrix.one_apply,j',anchor,h]

include H

omit [DecidableEq κ] [Fintype κ] in
lemma exits (i:κ) (j:ι) : ‖(A 0).mulVec (K.reed (A 0) i) j-(1:Matrix ι ι ℝ) j (e i)‖ ≤ u^3 * mist h r:= by
   have ht:=H.price; have hp:=mist_pos h r
   by_cases he:j∈K.W i
   · rw [stem K _ _ (H.attends K i).1 j he,sub_self,norm_zero]; positivity
   have hq:j≠e i:=fun hj=>he (hj.symm ▸ K.holds i)
   simp only [Matrix.one_apply,hq,if_false,sub_zero,mulVec,dotProduct]
   apply (norm_sum_le ..).trans
   have hm: h.Dust (l (e i)) (l j) ≤ mist h r:= departed h (H.stars i j he)
   have hz (k':ι): ‖A 0 j k' *K.reed (A 0) i k'‖ ≤ u^2*mist h r := by
     have ha : ‖A 0 j k'‖ ≤ u*h.Dust (l k') (l j):= ((H.core j k').2.value).trans_eq (by unfold Aim.Dust; rw [decay_comm])
     have hb := (H.ticking K i k').1
     rw [norm_mul]; apply (mul_le_mul ha hb (norm_nonneg _) (mul_nonneg (zero_le_one.trans ht) (h.dust_pos ..).le)).trans
     calc
       _ = u^2*(h.Dust (l (e i)) (l k')* h.Dust (l k') (l j)) := by ring
       _ ≤ _:= mul_le_mul_of_nonneg_left ((h.dust_link ..).trans hm) (by positivity)
   apply (Finset.sum_le_sum (fun k _=>hz k)).trans
   simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [pow_succ' u 2,mul_assoc]; exact mul_le_mul_of_nonneg_right H.tops (by positivity)

omit [DecidableEq κ] [Fintype κ] in
lemma closer (i:κ) (j:ι) : ‖K.reed (A 0) i j - ((A 0)⁻¹ j (e i))‖ ≤ u^5 * mist h r := by
   have ht:=H.price; have hp:=mist_pos h r; obtain ⟨hx,hy,hh⟩:= Aim.Camp.cost h H.camp
   let v:= K.reed (A 0) i; let b:ι→ℝ:=(1:Matrix ι ι ℝ).col (e i)
   let T:=(A 0)⁻¹; let y:=(A 0).mulVec v-b
   have hB : T.mulVec b= T.col (e i) := by
      funext j; rw [show T.col (e i) j=(T*1:Matrix ι ι ℝ) j (e i) from by simp]; rfl
   have hv:= show (T.mulVec y) j=v j-T j (e i) from by unfold y; rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hy, hB,Matrix.one_mulVec]; rfl
   have hG k: ‖T j k * y k‖ ≤ u^4*mist h r:= by
      have he: ‖T j k‖ ≤ u:= (hh j k).trans ((mul_le_of_le_one_right h.cap_pos.le (h.dust_le ..)).trans H.heat)
      rw [norm_mul,pow_succ' u 3,mul_assoc]; exact mul_le_mul he (exits K H i k) (norm_nonneg _) (zero_le_one.trans ht)
   change ‖v j-T j (e i)‖ ≤ _; rw [← hv]; apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun k _=>hG k)).trans ?_)
   simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [pow_succ' u 4,mul_assoc]; exact mul_le_mul_of_nonneg_right H.tops (by positivity)
end Leave

end Windows
end YM.Planned.PrimaryIntegral295.Glints
