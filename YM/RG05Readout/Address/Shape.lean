import YM.RG05Readout.Address.Size
/-!
# Energy grade restriction with holographic costs
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{d h:ℕ} {n:Side}{o:Site n}{R:Rep G n}{a b κ:ℝ}
variable (F:Labels.Frame G d)
-- weights for Mark vs δCost. no forgetting scalar
noncomputable def chunk (i:Letter d) (x:C.label (kept i)): Palette C d := Pi.single i x
@[simp] lemma chunk_self {i:Letter d}(x:C.label (kept i)) : chunk i x i=x:= Pi.single_eq_same ..
@[simp] lemma chunk_miss {i j:Letter d}(x:C.label (kept i)) (hj:j≠i): chunk i x j=0:= Pi.single_eq_of_ne hj _
lemma size_chunk (i:Letter d)(x:C.label (kept i)): size (chunk i x)=(C.labels.level (kept i)).coeffSize x:=by
    rw [bill_group,Finset.sum_eq_single i]; simp; intro j _ hj; simp [chunk_miss x hj,Frame.coeffSize]; simp
lemma cpart (i:Letter d){j:ℕ} (x:C.label (kept i)):
      clear C d j (chunk i x)=if depth i ≤ j then chunk i (Offsets.basisCut (C.labels.level (kept i)) (j - depth i) x) else 0 :=by
    funext z u
    by_cases hi:z=i
    · subst z
      change (if depth i+((C.labels.level (kept i)).grades u).1 ≤j then chunk i x i u else 0)=_
      rw [chunk_self]; split_ifs with h h' h'
      · rw [chunk_self]; change _=if ((C.labels.level (kept i)).grades u).1 ≤ j-depth i then _ else _; rw [if_pos (by omega)]
      · omega
      · rw [chunk_self]; change _=if ((C.labels.level (kept i)).grades u).1 ≤ j-depth i then _ else _; rw [if_neg (by omega)]
      rfl
    change (if weights (C:=C) ⟨z,u⟩ ≤ j then chunk i x z u else 0)=_
    split_ifs <;> simp [chunk_miss _ hi]

def ticket (i:Mark C d):Palette C d:= chunk i.1 (Size.axis (C.labels.level (kept i.1)) i.2)
lemma cardp (y:Palette C d): ∑ i:Mark C d,val y i • ticket i=y:=by
   rw [Fintype.sum_sigma];funext z; rw [Finset.sum_apply,Finset.sum_eq_single z];simp only [Finset.sum_apply,ticket,Pi.smul_apply,chunk_self]; exact Size.sum_axes _ _
   intro i _ hi; simp only [Finset.sum_apply,ticket,Pi.smul_apply,chunk_miss _ hi.symm,smul_zero, Finset.sum_const_zero]
   simp
lemma size_ticket (i:Mark C d):size (ticket i)=1:=by unfold ticket; rw [size_chunk,Size.size_axis]

def chargeN (L:Side) {d:ℕ}(i:Mark C d):ℝ:= (L.val:ℝ)^(d-weights i)
lemma charge_one (L:Side){d:ℕ} (i:Mark C d):1 ≤ chargeN L i:= one_le_pow₀ (by exact_mod_cast L.property)
lemma charge_global (L:Side){d:ℕ}(i:Mark C d):chargeN L i ≤ (L.val:ℝ)^d:=pow_le_pow_right₀ (by exact_mod_cast L.property) (Nat.sub_le ..)

lemma amplifies (L:Side)(y:Palette C d)(i:Mark C d):val (amplify d C L y) i=(chargeN L i:ℂ) * val y i:=by
   rcases i with ⟨i,j⟩
   change (↑L.val:ℂ)^(kept i-((C.labels.level (kept i)).grades j).1)* y i j=_
   unfold kept val chargeN weights; push_cast; rw [Nat.sub_sub]
lemma ticket_charge (L:Side)(i:Mark C d): amplify d C L (ticket i)= (chargeN L i:ℂ) • ticket i:=by
   obtain ⟨i,j⟩:=i; ext1 v; ext1 q
   by_cases hv:v=i
   · subst v
     by_cases h:q=j
     · subst q; exact amplifies L (ticket (Sigma.mk i j)) ⟨i,j⟩
     change val (amplify d C L _) ⟨i,q⟩=_ -- fill
     rw [amplifies]; unfold val ticket Size.axis; simp [Pi.single_eq_of_ne h]
   change val (amplify d C L _) (Sigma.mk v q)=_
   rw [amplifies]; unfold val ticket Size.axis; simp [chunk_miss _ hv]
lemma charge_sum (L:Side)(x:Palette C d):∑ i:Mark C d,‖val x i‖*chargeN L i=size (amplify d C L x):=by
   unfold size; apply Finset.sum_congr rfl; intro i _
   rw [amplifies,norm_mul,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (charge_one ..)),mul_comm]
lemma size_tuned (L:Side)(x:Palette C d):size (amplify d C L x) ≤ (L.val:ℝ)^d*size x:=by
   rw [← charge_sum,size,Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [mul_comm ‖val x i‖];exact mul_le_mul_of_nonneg_right (charge_global ..) (norm_nonneg _)
lemma size_refund (L:Side)(x:Palette C d): size x ≤ size (amplify d C L x):=by
   rw [← charge_sum,size]; apply Finset.sum_le_sum; intro i _; exact le_mul_of_one_le_right (norm_nonneg _) (charge_one ..)
section
open Trace.Physical Native
local notation "K"=> C.labels.level
local notation "S"=> C.localSection
variable (i:Letter d) (P:Coefficient (C.labels.level (kept i)) n)
lemma printed_one (hp:P.Format o C.params R)(hr:P.remBound o R κ a):
    Printed C d R o κ (glyph (readJ i 0) (invoice P o (S (kept i)) R)) (chunk i P.x) (chunk i (Trace.Physical.Germ.projection (C.labels.level (kept i)) C.params R.p.threshold o P)) a :=by
    let V(j:Letter d):= Extra.Histories.primary o (F:=C.labels.level (kept j)) 0; let Y:= update V i P; let t(j:Letter d):ℝ:= if j=i then a else 0
    have hκ:0<κ:=by obtain ⟨x,y,-,-,-,hκ,-⟩:=hr; exact hκ
    have hx j : j≠ i → Y j=V j:=fun he=> update_of_ne he ..
    have he : Y i=P:= update_self ..
    have hj(j:Letter d): (Y j).Format o C.params R ∧ (Y j).remBound o R κ (t j):=by
       by_cases hi:j=i
       · subst j; unfold t; rw [if_pos rfl, he]; exact ⟨hp,hr⟩
       unfold t; rw [hx j hi, if_neg hi]; exact ⟨primary_format _,primary_rem _ hκ⟩
    refine Printed.bind Y 0 Necklace.empty (fun j=> (hj j).1) (fun j=> (hj j).2) ?_ ?_ ?_ ?_
    · unfold together; rw [add_zero, Finset.sum_eq_single i,he]; intro j hj h; rw [hx j h]; unfold V; rw [invoice_zero,glyph_zero]; simp
    · funext j; by_cases hi:j=i; subst j; rw [he,chunk_self]; exact (chunk_miss _ hi).trans (hx j hi ▸ rfl)
    · funext j; by_cases hi:j=i
      · subst j; rw [he,chunk_self]
      rw [hx j hi,chunk_miss _ hi]
      unfold V Trace.Physical.Germ.projection; simp only [Extra.Histories.primary, Pi.zero_apply]; simp_rw [Trace.Physical.Germ.vector]
      have hV: Trace.Physical.Germ.label C.params o (0:Config G n→ℂ) (kept j)=0:=by
         unfold Trace.Physical.Germ.label; split; next h=>
            apply Next.Foundations.JetTest.unique h.choose_spec
            apply (Next.Foundations.jetTest_zero_iff ..).mpr
            exact fun x=>⟨contDiffAt_const,fun k _=>by simp⟩
         next=>rfl
      simp [hV]
    simp [t]
omit i P
lemma printed_high (φ:PulseC)(hf:Tail d φ)(ht:Priced d φ b)(p:Coefficient (C.labels.level 0) n) (hp:p.Format o C.params R)(hy:p.remBound o R κ a):
    Printed C d R o κ (glyph φ (invoice p o (S 0) R)) 0 0 (b*((K 0).coeffSize p.x+a)):=by
   have hκ:0 < κ:=by obtain ⟨b,c,-,-,-,h,-⟩:=hy; exact h
   rcases Printed.blank (d:=d) (o:=o) (R:=R) (C:=C) hκ with @⟨V,X,v,w,Y,H,hA,hp',he,hq,hC⟩
   refine Printed.bind V _ (.chain φ hf ht p hp hy Y) H hA ?_ he hq ?_
   · rw [add_left_comm,hp',add_zero]
   rw [add_left_comm]; exact (add_le_add_right hC _).trans_eq (add_zero _)
end
end YM.RG05Readout.Address
