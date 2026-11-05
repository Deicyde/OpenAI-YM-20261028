import YM.RG08.Vale.Froth
/-!
# Applying pre-length row Newton gains, pol/exp. No count of lengths or radii at costs
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open Function Filter Matrix Lattice Bloch Exterior Precision Laurent Next.Free Work.F08 RG
open Quire Shade Planned.PrimaryIntegral295 Push.AbsoluteSums Finset
open scoped Topology ContDiff Classical BigOperators
variable {ι : Type} {n : ℕ} {A C : ℝ}
-- evaluate scalar combinations only, then test full bounds
section test
variable {v p : ι →ℝ} {w:ι→ Cover→ℝ}

def pot (t f : ι→ℝ) (s : Finset ι) := ∑ i∈s,t i*f i
lemma pig (h:0≤v): Charge v p A ↔ (∀ (g : ι→ℝ), (∀ i, ‖g i‖≤v i)→ ∀ s, ‖pot g p s‖ ≤ A) := by
  constructor
  · intro hx g hv s; apply (norm_sum_le ..).trans
    exact (sum_le_sum (g:=fun i=> v i*‖p i‖) (fun i _=> by rw [norm_mul]; gcongr; exact hv _)).trans ((hx.2.1.sum_le_tsum _ (fun i _=> hx.1 _)).trans hx.2.2)
  intro he
  let g i:= if p i<0 then -(v i) else v i
  have hh i : ‖g i‖≤v i := by unfold g; split <;> simp [Real.norm_of_nonneg (show 0≤v i from h i)]
  have hx : ∀ s:Finset ι,∑ i∈s,v i*‖p i‖ ≤ A := by
    intro s; apply le_trans _ (he g hh s); apply le_trans _ (Real.le_norm_self _)
    exact sum_le_sum fun i _=> by unfold g; split_ifs <;> rename_i ht; simp [Real.norm_of_nonpos ht.le]; simp [Real.norm_of_nonneg (le_of_not_gt ht)]
  have hu : 0 ≤ fun i=> v i*‖p i‖ := fun i=>mul_nonneg (h i) (norm_nonneg _)
  exact ⟨hu,summable_of_sum_le hu hx,Real.tsum_le_of_sum_le hu hx⟩
private def stem (t : ι→ℝ) (u:ι→Cover→ℝ)(s:Finset ι) (x:Cover):= pot t (fun i=> u i x) s
private lemma offling (t:ι→ℝ)(w:ι→Cover→ℝ)(s:Finset ι)(j:Axis): Trellis.offset (stem t w s) j = stem t (fun i=> Trellis.offset (w i) j) s := by funext x; simp only [stem,pot,Trellis.offset,mul_sub,sum_sub_distrib]
private lemma woven_l (t:ι→ℝ)(w:ι→Cover→ℝ)(s:Finset ι)(l:List Axis): Trellis.delta (stem t w s) l = stem t (fun i=> Trellis.delta (w i) l) s := by
  induction l with
  | nil=>rfl
  | cons i l ih=> rw [Trellis.delta,ih,offling]; rfl
lemma sectors_l (t:ι→ℝ)(w:ι→Cover→ℝ)(s:Finset ι)(n:ℕ)(x:E4):
    Trellis.sector n (stem t w s) x=pot t (fun i=> Trellis.sector n (w i) x) s := by
  induction n generalizing w x with
  | zero=>rfl
  | succ n ih=>
    simp only [Trellis.sector,offling,ih,pot,smul_eq_mul]; simp_rw [mul_sum]
    rw [sum_comm]; apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro a _; ring
lemma surplus_l (t:ι→ℝ)(w:ι→Cover→ℝ)(s:Finset ι)(n:ℕ)(x:Cover):
    Trellis.surplus (stem t w s) n x=pot t (fun i=> Trellis.surplus (w i) n x) s := by
  unfold Trellis.surplus pot; simp only [Pi.sub_apply, mul_sub,sum_sub_distrib,Trellis.fitting,sectors_l]
  unfold pot; congr 1; simp_rw [mul_sum]; exact sum_comm
lemma sectors_paid (h:0≤v) (n : ℕ): ∃ C:ℝ,1≤C ∧ ∀ (B:ℝ)(w:ι→ Cover→ℝ),0≤B →
    (∀ l:List Axis,l.length=n → Charge v (fun i=>Trellis.delta (w i) l 0) B)→
    ∀ x, Charge v (fun i=> Trellis.sector n (w i) (Place.seat x)) (C*B*dime n x) := by
  obtain ⟨C,hC,H⟩:=Trellis.price_point n (E:=ℝ)
  refine ⟨C,hC,fun B w hB hW x=> (pig h).2 fun g hg s=> ?_⟩
  rw [← sectors_l]; refine (H _ B hB (fun l hl=>?_) (Place.seat x)).trans ?_
  · rw [woven_l]; exact (pig h).1 (hW l hl) g hg s
  unfold dime Carrier.liftCost; gcongr; exact Carrier.shade_seat x
lemma surplus_paid (h:0≤v) (n M : ℕ)(w:ι→ Cover→ℝ)(hA:0≤A)(he:∀ l:List Axis,l.length=n→∀ x:Cover,size x ≤ M→ Charge v (fun i=>Trellis.delta (w i) l x) A) (x:Cover)(hp:size x≤M):
    Charge v (fun i=> Trellis.surplus (w i) n x) (A*(size x:ℝ)^n) := by
  apply (pig h).mpr; intro g hg s; rw [←surplus_l]; apply Trellis.accrue _ _ _ _ hA _ x hp; intro l hl y hy; rw [woven_l]; exact (pig h).1 (he l hl y hy) g hg s
end test

variable {α β:Type} [Fintype β] {L:Side}
variable (σ B:ℝ) (hs : 0<σ)(hp:0≤B)
abbrev height (L:Side)(j:ℕ) : ℝ := (L.val:ℝ)⁻¹^j
lemma height_p (L:Side)(j:ℕ): 0<height L j:= by unfold height; positivity
lemma height_one {i j:ℕ}(L:Side)(hp:i≤j): height L j ≤ height L i := pow_le_pow_of_le_one (Carrier.unitStep_pos L).le (Carrier.unitStep_le ..) hp
lemma height_ge (L:Side){x:Cover} (h : L.val ≤ size x) (n:ℕ) : 1 ≤ height L n * dime n x := by
  unfold height dime Carrier.liftCost; rw [← mul_pow]; refine one_le_pow₀ ?_; field_simp; have he : (L.val:ℝ) ≤ size x:= by exact_mod_cast h
  linarith
structure PaysPath (Q : Cross L α β)(v:ℝ)(A:ℝ)(d:ℕ) : Prop where
  odd : Odd L.val
  offsets : ∀ l:List Axis,l.length≤d→ (advanceC L Q l).strip v (A*height L (l.length+1))
-- for both weight conventions before repeated gain
structure TakesP (Q : Cross L α β) (w: Cover×α→ℝ)(v:Cover×β→ℝ) (d:ℕ) (C:ℝ) : Prop where
  first : 1 ≤ w
  second : 1 ≤ v
  size_bound : ∀ x:Cover×α,dime d x.1 ≤ C * w x
  main_bound : ∀ (p:Site L)(l: List Axis), l.length ≤ d →∀ i:α,∀ x:Cover,size x≤L.val →
    Charge v (fun k=> Trellis.delta (fun x=> node p Q (x,i) k) l x) (C * height L (l.length+1))
  far_bound : ∀ (p:Site L)(x:Cover×α),L.val ≤ size x.1→ Charge v (node p Q x) (C*height L (d+1)*w x)

private lemma up {a:Cover} (h:size a≤L.val): (L.val:ℝ)⁻¹ * size a ≤ 1 := (mul_le_mul_of_nonneg_left (show ((size a:ℕ):ℝ)≤(L.val:ℝ) by exact_mod_cast h) (by positivity)).trans_eq (inv_mul_cancel₀ (by positivity))
include hs hp
lemma growthP (u d : ℕ)(h:d≤u):∃ C:ℝ,1≤C ∧ ∀ (L:Side)(Q:Cross L α β), PaysPath Q σ B d → TakesP Q (rug u) (rug u) d C := by
  let f:= σ⁻¹^u*u.factorial*Real.exp σ; let t:= f*(((Fintype.card β:ℕ):ℝ)*B); let C:=(10:ℝ)^u*t
  have ht:0≤C := by unfold C t f; positivity
  have hC:1≤1+C:=le_add_of_nonneg_right ht
  have hf : 0≤f := by unfold f; positivity
  refine ⟨_,hC, fun L Q hv=> ⟨rug_one,rug_one, ?_,fun p l hl i x hx=>?_,fun p x hx=>?_⟩⟩
  · intro x; apply le_trans (dime_more h _); apply le_mul_of_one_le_left _ hC; exact Carrier.liftCost_pos ..
  · simp_rw [foams hv.odd]; apply Ink.raise (nodePol (hv.offsets l hl) hs p u (x,i)); have hw := up hx
    calc
      _ ≤ 10^u * (f*(Fintype.card β*(B*height L (l.length+1)))) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by dsimp only; linarith) _) (by positivity [height_p L (l.length+1)])
      _ ≤ _ := by unfold C t; rw [← mul_assoc _ B,←mul_assoc f,←mul_assoc]; gcongr; simp
  apply Ink.raise (nodePol (hv.offsets [] (by simp)) hs p u x) -- argument
  let y:=(L.val:ℝ)⁻¹; have hy:0≤y:= by unfold y; positivity
  have hq : 1 ≤ y * (size x.1) := calc
    1 = y*(L.val:ℝ) := (inv_mul_cancel₀ (by positivity : (L.val:ℝ)≠0)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hx) hy
  calc
    _ ≤ (10*(y*(1+(size x.1:ℝ))))^u * (f * ((Fintype.card β:ℝ)*(B*y))) := by
      simp only [height,pow_one,List.length_nil,Nat.zero_add]; change _*(f*(_*(B*y))) ≤ _
      apply mul_le_mul_of_nonneg_right _ (by positivity); exact pow_le_pow_left₀ (show 0≤5*(1+y*size x.1) by positivity) (by nlinarith) _
    _ = C*height L (u+1)*rug u x := by unfold C t rug dime Carrier.liftCost height y; rw [mul_pow, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul (le_add_of_nonneg_left zero_le_one) (height_one L (Nat.add_le_add_right h 1)) (height_p ..).le (by positivity)) (Carrier.liftCost_pos ..)
end YM.RG08.Vale
