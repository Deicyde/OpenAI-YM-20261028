import YM.RG08.Run.Silt
/-! # Cards on softened or unsoftened polynomial channel. Preserve amplitude factors on comparison calls. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {r s D j i k n e:ℕ}{I J Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]{α β:I→Type}
variable {x p q y ρ δ ξ w v z:I→ℝ}{U V A B : ∀ i, Rooted Y (α i) r}{R M:∀ i,Rooted Y (β i) r}
structure Card (k:ℕ)(y δ:I→ℝ)(U:∀ i, Rooted Y (α i) r)(v:I→ℝ) : Prop where
   money : ∃ C,Weighed y C ∧ ∀ i, cis k (v i) (U i) (C i*δ i)
structure Drum (k:ℕ)(y δ ρ:I→ℝ)(U V:∀ i, Rooted Y (α i) r)(v:I→ℝ):Prop where
   first : Card k y ρ U v
   second : Card k y ρ V v
   funds : Card k y (δ*ρ) (U-V) v
lemma Card.even (h : Card k y δ U v)(hx:0≤v)(i): Pens (U i):= Ink.pens (h.money.choose_spec.2 i) (tailp (hx i))
lemma Card.mold (h:Card k y δ U v)(b:J→I):Card k (fun i=>y (b i)) (fun i=>δ (b i)) (fun i=>U (b i)) (fun i=> v (b i)) := ⟨_,h.money.choose_spec.1.transfer b,fun i=>h.money.choose_spec.2 (b i)⟩
lemma Card.more (h:Card k y δ U v)(he:Card k y δ V v)(hx:0≤v)(hp:Audience y): Card k y δ (U+V) v:= by
    obtain ⟨A,hA,H⟩:=h.money; obtain ⟨B,hB,H'⟩:=he.money; exact ⟨_,hA.plus hB hp,fun i=> Ink.raise (Ink.plus (H i) (H' i) (fun j=> (tailp (hx i) j).trans' zero_le_one)) (by rw [Pi.add_apply,add_mul])⟩
lemma Card.neg (h:Card k y δ U v): Card k y δ (-U) v:=⟨_,h.money.choose_spec.1,fun i=> Ink.neg (h.money.choose_spec.2 i)⟩
lemma Card.less (h:Card k y δ U v)(he:Card k y δ V v)(hx:0≤v)(hp:Audience y): Card k y δ (U-V) v:= (sub_eq_add_neg U V).symm ▸ h.more he.neg hx hp -- orientation?
lemma Card.awake (h:Card k y ρ U v)(hh:0≤ρ)(he: Dig y δ x) : Card k y (δ*ρ) (fun i=> x i • U i) v:= by
    obtain ⟨B,hB,H⟩:= h.money; obtain ⟨A,hA,Hx⟩:= he.asset; refine ⟨_, hA.times hB,fun i=> Ink.raise (Ink.scale (H i) (x i)) ?_⟩
    exact (mul_le_mul_of_nonneg_right (Hx i) (mul_nonneg (hB.positive _) (hh _))).trans_eq (mul_mul_mul_comm ..)
lemma Card.raise (h:Card k y δ U v)(hp:δ ≤ z) : Card k y z U v:= ⟨_,h.money.choose_spec.1,fun i=> Ink.raise (h.money.choose_spec.2 i) (mul_le_mul_of_nonneg_left (hp i) (h.money.choose_spec.1.positive i))⟩ -- add z
lemma Card.lesser (h:Card k y (z*δ) U v)(he: Weighed y z) : Card k y δ U v := ⟨_,h.money.choose_spec.1.times he,fun i=> by simpa only [Pi.mul_apply,mul_assoc] using h.money.choose_spec.2 i⟩
lemma Card.zero : Card k y δ (0:∀ i,Rooted Y (α i) r) v := ⟨0,Weighed.zero,fun i=>by rw [Pi.zero_apply (M:=fun i=>Rooted Y (α i) r),Pi.zero_apply,zero_mul]; exact Ink.none ..⟩
lemma Card.cost (h:Card k y δ U v)(he:Weighed y (fun i=> ‖p i‖)) : Card k y δ (fun i=>p i • U i) v:= ⟨_,he.times h.money.choose_spec.1,fun i=> by rw [Pi.mul_apply,mul_assoc]; exact Ink.scale (h.money.choose_spec.2 i) _⟩
lemma Card.group (s:Finset J)(he:Audience y)(hv:0≤v){F:J→∀ i,Rooted Y (α i) r}(h:∀ i∈s,Card k y δ (F i) v): Card k y δ (fun i=> ∑ j∈s,F j i) v:= by
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Card.zero
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).more (ih fun j hj=> h j (mem_insert_of_mem hj)) hv he
lemma Drum.mold (h:Drum k y δ ρ U V v)(b:J→I): Drum k (fun i=>y (b i)) (fun i=>δ (b i)) (fun i=>ρ (b i)) (fun i=>U (b i)) (fun i=>V (b i)) (fun i=>v (b i)) := ⟨h.first.mold b,h.second.mold b,h.funds.mold b⟩
lemma Drum.home (h:Card k y ρ U v): Drum k y δ ρ U U v:=⟨h,h,by rw [sub_self]; exact Card.zero⟩
lemma Drum.more (h:Drum k y δ ρ U V v)(hz: Drum k y δ ρ A B v)(hv:0≤v)(hp:Audience y): Drum k y δ ρ (U+A) (V+B) v:= ⟨h.first.more hz.first hv hp,h.second.more hz.second hv hp,by rw [show (U+A)-(V+B)=(U-V)+(A-B) by abel]; exact h.funds.more hz.funds hv hp⟩
lemma Drum.zero : Drum k y δ ρ (0:∀ i,Rooted Y (α i) r) 0 v:= Drum.home Card.zero
lemma Drum.sc (h:Drum k y δ ρ U V v)(hp: Lease y δ p q)(he:0≤ρ)(hh: Audience y)(hv:0≤v): Drum k y δ ρ (fun i=>p i • U i) (fun i=> q i • V i) v:= by
   refine ⟨h.first.cost hp.has,h.second.cost hp.also,?_⟩
   let X i:=(p-q) i • U i; let P' i:= q i • (U-V) i
   rw [show _-_ = X+P' from funext fun i=>by simp only [Pi.sub_apply,Pi.add_apply,X,P',smul_sub]; rw [_root_.sub_smul (p i) (q i) (U i)]; abel]
   exact (h.first.awake he (Dig.of_lease hp)).more (h.funds.cost hp.also) hv hh
lemma Drum.weight (h:Drum k y δ ρ U V v)(p:ℝ): Drum k y δ ρ (p • U) (p • V) v:= ⟨h.first.cost (Weighed.constant _ (norm_nonneg p)),h.second.cost (Weighed.constant _ (norm_nonneg p)),by rw [← smul_sub]; exact h.funds.cost (Weighed.constant _ (norm_nonneg p))⟩
lemma Drum.group (s:Finset J)(he:Audience y)(hv:0≤v){F H:J→∀ i,Rooted Y (α i) r}(h:∀ i∈s,Drum k y δ ρ (F i) (H i) v): Drum k y δ ρ (fun i=>∑ j∈s,F j i) (fun i=>∑ j∈s,H j i) v:= by
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Drum.zero
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).more (ih fun j hj=> h j (mem_insert_of_mem hj)) hv he
lemma Drum.grantor (h:Drum k y δ ρ U V v)(m:ℕ):Drum k y δ ρ (fun i=>grant m (U i)) (fun i=> grant m (V i)) v:= by
    unfold grant; split; next h'=> subst m; exact h
    exact Drum.zero
lemma Drum.sewn (h:Drum k y δ ρ U V v)(hx:0≤v): Drum k y δ ρ (fun i=>sew (U i)) (fun i=> sew (V i)) v:= by
    have hh δ (U:∀ i,Rooted Y (α i) r)(h:Card k y δ U v): Card k y δ (fun i=> sew (U i)) v:= ⟨_,h.money.choose_spec.1,fun i=> sew_cis (h.money.choose_spec.2 i) (hx i)⟩
    refine ⟨hh _ _ h.first,hh _ _ h.second,?_⟩; rw [show _-_=(fun i=>sew ((U-V) i)) from funext fun i=> Eq.symm sew_sub]; exact hh _ _ h.funds
lemma utterBuy (k:ℕ)(h:Weighed y (fun i=>(v i)⁻¹))(hp:v≤1): Weighed y (fun i=> utter k (v i)):= by
  have hx:= (Weighed.constant y (Real.exp_pos 1|>.le)).mono (fun i:I=>(Real.exp_pos (v i)).le) (fun i=> Real.exp_monotone (show v i≤1 from hp i))
  exact ((h.powers k).times (Weighed.constant _ (by positivity))).times hx
lemma ofTin (h:Tin y δ U v)(hp:∀ i,0<v i)(hv:Weighed y (fun i=> utter k (v i))): Card k y δ U 1 := by
  obtain ⟨A,hA,H⟩:=h.serves; refine ⟨_,hv.times hA,fun i=>?_⟩; rw [Pi.mul_apply, mul_assoc] 
  have ht: Glow (fun j=>‖U i j‖) (v i) (A i*δ i):= by simpa only [Quire.Lit,Glow,Charge,Quire.Ink,norm_norm] using! H i
  have hh:=glow_moment ht (hp _) k; unfold cis Quire.Ink; simp only [tailP,Pi.one_apply,one_mul]; simpa only [norm_norm] using hh
end YM.RG08.Run
