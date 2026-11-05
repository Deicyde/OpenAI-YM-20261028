import YM.RG08.Atlas.Aim

noncomputable section
set_option autoImplicit false
namespace YM.RG08.Mount
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate Symmetry Steam Cairn Cloud
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}{C:Castle G}
lemma bell_sum (h:S.patch.Branches S.kernel G)(t:S.Choices)(e:ℕ): showV (unveil (bell h) c) e=tap e (tax 2 (flask (fair S t))):=by
 unfold showV unveil bell; rw [sum_eq_single_of_mem (e+2) (by simp)]; swap
 · intro b hb hB; simp [hB]; split <;> rename_i hn
   · rw [blank _ _ rfl];exact parley_zero
   exact parley_zero
 simp only [Nat.zero_lt_succ,dif_pos,↓reduceIte,Tack.parade_read h t, Camera.audited]

lemma dusk_sum (S:StepData c f){B:ChartRatio G}(hB:LocalRatio B)(e:ℕ): showV (unveil (dusk S.patch B) c) e=tap e (aroma S B):=by
 unfold showV unveil dusk;rw [sum_eq_single_of_mem e (by simp)];swap
 · intro b hb hK;simp_rw [if_neg (show ¬(0 < e ∧ e=b) from fun he=>hK he.2.symm)]; split <;> rename_i hn
   · rw [blank _ _ rfl]; exact parley_zero
   exact parley_zero
 by_cases he:0<e
 · simp only [he,dif_pos,if_pos,and_self];exact (aroma_read hB S ⟨0,he⟩).symm
 rw [show e=0 by omega];simp only [dif_neg (Nat.lt_irrefl 0),parley_zero,aroma,censor,tap,flask,PowerSeries.coeff_mk,Camera.print,Cairn.named hB,map_zero]

def slaw {I:Type}(F:Grain (Market I))(e:ℕ):Prop:=∀ n,∃ σ p:ℝ,0<σ ∧ 0 ≤ p ∧ Held (carpet _) σ p (F e n)
lemma castle_room (P:Patch)(C:Castle G)(h:Stable C)(e:ℕ): slaw (castle P C) e:=by
 intro n;obtain ⟨a,b,ha,hb,H⟩:=carpet_demand C h e n; exact ⟨_,_,ha,mul_nonneg (Real.exp_pos _).le hb,box_cost H ha.le _⟩
lemma bell_room {P:Patch}(h:P.Branches K G)(e:ℕ):slaw (bell h) e:=by
 intro n; unfold bell; split <;> rename_i hn
 · exact ⟨1,_,zero_lt_one,Finset.sum_nonneg (fun i _=> price_nn ..),(parade_bill h n (σ:=1)).1⟩
 exact ⟨1,0,zero_lt_one,le_rfl,zero_held⟩
lemma dusk_room (P:Patch)(B:ChartRatio G)(e:ℕ):slaw (dusk P B) e:=by
 intro n;unfold dusk; split <;> rename_i hn
 · refine ⟨1,_,zero_lt_one,mul_nonneg (Real.exp_pos _).le (layer_nn ..),box_cost (vanity_bill B n (σ:=1)).1 zero_le_one _⟩
 exact ⟨1,0,zero_lt_one,le_rfl,zero_held⟩
lemma slaw.twain {A B:Grain (Market I)}{e n:ℕ}(ha:slaw A e)(hb:slaw B e):∃ σ a b:ℝ,0 < σ ∧ 0 ≤ a∧ 0 ≤ b∧ Held (carpet _) σ a (A e n)∧Held (carpet _) σ b (B e n):=by
 obtain ⟨a,A,ah,Ah,h⟩:= ha n;obtain ⟨b,B,bh,Bh,H⟩:=hb n; exact ⟨_,_,_,lt_min ah bh,Ah,Bh,h.mono (min_le_left a b) le_rfl (fun _=>le_rfl), H.mono (min_le_right a b) le_rfl (fun _=>le_rfl)⟩
lemma slaw.add{A B:Grain (Market I)}(ha:slaw A e)(hb:slaw B e):slaw (A+B) e:=by intro n;obtain ⟨s,a,b,hs,x,y,h,v⟩:= ha.twain hb (n:=n); exact ⟨_,_,hs,add_nonneg x y,h.add v x y⟩
lemma slaw.neg{A:Grain (Market I)}(ha:slaw A e):slaw (-A) e:=by intro n;obtain ⟨s,a,hs,x,h⟩:=ha n;exact ⟨_,_,hs,x,h.neg⟩

-- scalar enrolment even if extensive, here subtraction preserves zero disguise
lemma unveil_neg (A:Grain (Market I))(P:Side)(e:ℕ): unveil (-A) P e= -unveil A P e:=by
 funext n y; unfold unveil; split <;> rename_i hn
 · simp_rw [Pi.neg_apply,dif_pos hn,pour_at ]; simp [tsum_neg]
 · simp [Pi.neg_apply,hn]
lemma unveil_add {A B:Grain (Market I)}{e:ℕ}(ha:slaw A e)(hb:slaw B e)(P):unveil (A+B) P e=unveil A P e+unveil B P e:=by
 funext n y; unfold unveil; split <;> rename_i hn
 · obtain ⟨s,a,b,hs,_,_,h,H⟩:=ha.twain hb (n:=n)
   have ht (f:Flake n (Market I))(K)(hh:Held (carpet _) s K f) : Summable (fun x:↥(lantern (i:= (⟨0,hn⟩ :Fin n)) y)=> f x.val):= by
      apply Summable.of_norm;exact ((cell_sum hh hs.le ⟨0,hn⟩ (reach (y ⟨0,hn⟩))).comp_injective (Subtype.val_injective (p:=fun x=>x∈lantern ⟨0,hn⟩ y))).congr (by intro x; rw [Function.comp_apply,if_pos x.property.1,Real.norm_eq_abs])
   simp_rw [Pi.add_apply,dif_pos hn,pour_at] -- n y two add
   exact (ht _ a h).tsum_add (ht _ b H)
 · simp [Pi.add_apply,hn]

variable [Fintype I]
lemma show_neg (A:Grain (Market I))(P:Side)(e):showV (unveil (-A) P) e= -showV (unveil A P) e:=by
 unfold showV; rw [←Finset.sum_neg_distrib];simp_rw [unveil_neg,Pi.neg_apply];apply sum_congr rfl;intro j _; have he(F:Flake j (Cove P I)): -F=(-1:ℝ) • F:=by simp
 rw [he,parley_smul];simp
lemma show_add{A B:Grain (Market I)}{e:ℕ}(h:slaw A e)(v:slaw B e)(P):showV (unveil (A+B) P) e=showV (unveil A P) e+showV (unveil B P) e:=by unfold showV; simp_rw [unveil_add h v,Pi.add_apply,parley_add]; rw [sum_add_distrib]

lemma china_tap (h:S.patch.Branches S.kernel G)(t:S.Choices)(C:Castle G)(hh:Stable C)(e): tap e (china h C)=
 -((∑ i∈range (e+1),∑ r∈range (i+1), tap e (leaf S (C r i) (stick r) i))+tap e (tax 2 (flask (fair S t)))):=by
 unfold tap china Glyph.stock; rw [PowerSeries.coeff_mk,Mount.sweep,show_neg,show_add (castle_room S.patch C hh e) (bell_room h e),bell_sum h t, castle_sum S hh]

lemma stock_inlet (h:S.patch.Branches S.kernel G){B:ChartRatio G}(hB:LocalRatio B)(C:Castle G)(hh:Stable C): stock (unveil (inlet h C B) c)=china h C+aroma S B-liftInn (tap 0 (china h C)):=by
 ext e :1
 change tap _ _=_
 have he:slaw (Mount.sweep h C) e:= ((castle_room S.patch C hh e).add (bell_room h e)).neg
 unfold tap china Glyph.stock; rw [map_sub,map_add,PowerSeries.coeff_mk,PowerSeries.coeff_mk,PowerSeries.coeff_C]
 by_cases hf:0<e
 · have hv:showV (unveil (inlet h C B) c) e=showV (unveil (ghost h C B) c) e:=by unfold showV unveil inlet;rw [if_pos hf]
   rw [hv,if_neg (by omega),sub_zero,ghost,show_add he (dusk_room S.patch B e), dusk_sum S hB] 
 rw [show e=0 by omega]; simp only [showV,unveil,inlet,Nat.lt_irrefl,↓reduceIte]
 have hd(n:ℕ):parley (I:=Epic S.patch G c) (if h:0<n then pour ((0 : (k:ℕ)→ Flake k (Market (Head S.patch G))) n) ⟨0,h⟩ else 0) =0:=by
    split;next he=> change parley (pour (P:=c) (n:=n) (0: Flake n (Market (Head S.patch G))) _) =0; rw [blank _ _ rfl,parley_zero]
    exact parley_zero
 simp_rw [hd,Finset.sum_const_zero,←show ∀ (p:Port (Epic S.patch G c)),tap 0 p=PowerSeries.coeff 0 p from fun _=>rfl,aroma,Cairn.censor, tap,flask,PowerSeries.coeff_mk,Camera.print,Cairn.named hB,map_zero]; try simp -- china maybe unfolded
 change (0:Inn (Epic S.patch G c))=_-_ ; unfold showV unveil;rw [sub_self]
end YM.RG08.Mount
