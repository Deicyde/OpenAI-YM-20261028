import YM.RG08.Vale.Tumble
import YM.Planned.PRIMARY_INTEGRAL_295.Savings
/-!
# Relative tested row budgets. Same true lift nonwrapping, any arity
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
variable {E F α β:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
variable {D k u r:ℕ}{m c f L:Side}
variable {V:Rooted E α r}{w w' B σ A:ℝ}{Q:Cross L α β}
def rug (u : ℕ): Cover×α→ℝ := fun i=> dime u i.1
def plyH (u: ℝ): Cover×α→ℝ := fun i=> Real.exp (u*size i.1)
lemma rug_one : 1 ≤ rug u (α:=α) := fun _=> Carrier.liftCost_ge ..
lemma plyH_one (hw:0≤w): 1 ≤ plyH w (α:=α) := fun _=> Real.one_le_exp (by positivity)

def node (p:Site L)(Q:Cross L α β): Paper α β := fun x y=> Q (arrives p x.1,x.2) y.2 (y.1-carry p x.1)
lemma carries_add (p : Site L)(a b:Cover):
    carry p (a+b)=carry p a+carry (arrives p a) b := by
  have h:= carry_spec p a; have ht:= carry_spec p (a+b); have hu:=carry_spec (arrives p a) b
  rw [show arrives (arrives p a) b= _ from (by simp [arrives,add_assoc] : arrives (arrives p a) b=arrives p (a+b))] at hu
  have he : L.val • carry p (a+b)=L.val • (carry p a+carry (arrives p a) b) := by
    apply add_left_cancel (a:=lift (arrives p (a+b))); rw [← ht,smul_add, ← add_assoc (lift p) a, h,add_right_comm (lift (arrives p a)),hu]; abel
  ext i; apply mul_left_cancel₀ (show ((L.val:ℕ):ℤ)≠0 by positivity); exact (by simpa only [Pi.smul_apply,nsmul_eq_mul] using congr_fun he i)
lemma foams (h:Odd L.val)(l:List Axis)(p:Site L)(a:α)(y:Cover×β)(Q:Cross L α β):
    Trellis.delta (fun x=>node p Q (x,a) y) l=fun x=>node p (advanceC L Q l) (x,a) y := by
  induction l with
  | nil=> rfl
  | cons i l ih=>
    let A:= advanceC L Q l; let f x:=node p A (x,a) y
    rw [Trellis.delta,ih]; funext x; unfold Trellis.offset
    change f _ - f x = node p (forwardC L A i) (x,a) y
    unfold f node
    simp only [carries_add,carry_crank L h]
    rw [show arrives p (x+step i)=arrives p x+step i from by simp [arrives,add_assoc]]
    unfold forwardC carryStep mid; dsimp only; split_ifs <;> simp [sub_add_eq_sub_sub]
lemma centerd (p:Site L)(x:Cover) : ((size (carry p x):ℕ):ℝ) ≤ 4+(L.val:ℝ)⁻¹*size x := by
  apply le_of_mul_le_mul_left _ (show 0 < (L.val:ℝ) by positivity)
  calc
    _ ≤ size x + (4:ℝ)*L.val := by exact_mod_cast block_carry p x
    _ = _ := by field_simp; ring
variable [Fintype β]
lemma node0 (h:Q.strip σ A) (p:Site L) (a : Cover×α): Charge (fun y:Cover×β=> Real.exp (σ*size (y.1-carry p a.1))) (node p Q a) (Fintype.card β*A) := by
  let e: Cover×β≃Cover×β:= Equiv.prodCongr (Equiv.addRight (-carry p a.1)) (Equiv.refl _)
  have he := budget_pull e e.injective (row_fitter h (arrives p a.1, a.2))
  simpa only [Charge,node,e,Equiv.prodCongr_apply, Equiv.refl_apply,Function.comp_apply,sub_eq_add_neg] using! he
lemma nodePol (h:Q.strip σ A)(hs:0<σ) (p:Site L)(u:ℕ)(i : Cover×α): Charge (rug u) (node p Q i)
    ((5*(1+(L.val:ℝ)⁻¹*size i.1))^u * ((σ⁻¹^u*u.factorial*Real.exp σ)*(Fintype.card β*A))) := by
  let a:= (L.val:ℝ)⁻¹; have hp :0≤a:= by unfold a; positivity
  let c := carry p i.1
  have hx := centerd p i.1; have hc : dime u c ≤ (5*(1+a*size i.1))^u := pow_le_pow_left₀ (show 0 ≤ 1+(size c:ℝ) by positivity) (by change 1 + (size (carry p _):ℝ) ≤ _; dsimp only [a]; linarith [show 0≤ a*size i.1 by positivity]) _
  have he (y:Cover×β): dime u (y.1-c)≤ σ⁻¹^u*u.factorial*Real.exp σ*Real.exp (σ*size (y.1-c)) := (polynomial_price hs (show 0≤1+(size (y.1-c):ℝ) by positivity) u).trans_eq (by rw [mul_add,mul_one,Real.exp_add]; ring)
  have hv (y:Cover×β): dime u y.1 ≤ dime u (y.1-c) * dime u c := by convert Carrier.liftCost_add u (y.1-c) c using 2; simp
  refine budget_mono (budget_scale (show 0 ≤ (5*(1+(L.val:ℝ)⁻¹*size i.1))^u by positivity) (budget_scale (show 0≤ σ⁻¹^u*u.factorial*Real.exp σ by positivity) (node0 h p i))) (fun y=> mul_nonneg (Carrier.liftCost_pos ..) (norm_nonneg _)) (fun y=>?_)
  apply (mul_le_mul_of_nonneg_right ((hv y).trans (mul_le_mul (he y) hc (Carrier.liftCost_pos ..) (by positivity))) (norm_nonneg _)).trans_eq; unfold c a; ring
lemma nodeExp (h:Q.strip σ A)(he:0≤w')(ht:w'≤σ)(p:Site L) (i:Cover×α): Charge (plyH w') (node p Q i) (Real.exp (w'*(4+(L.val:ℝ)⁻¹*size i.1))*(Fintype.card β*A)) := by
  let c:=carry p i.1; let K:=4+(L.val:ℝ)⁻¹*size i.1
  apply budget_mono (budget_scale (Real.exp_pos (w'*K)).le (node0 h p i)) (fun y=> mul_nonneg (Real.exp_pos ..).le (norm_nonneg _)); intro i
  have hp : ((size i.1:ℕ):ℝ) ≤ size (i.1-c) +K := by
    calc _ ≤ size (i.1-c)+ ((size c:ℕ):ℝ) := by exact_mod_cast (le_trans (show size i.1 ≤ size ((i.1-c)+c) by simp) (size_add ..))
         _ ≤ _ := add_le_add_right (centerd ..) _
  rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right (Real.exp_add .. ▸ Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  nlinarith only [mul_le_mul_of_nonneg_left hp he,mul_le_mul_of_nonneg_right ht (show 0 ≤ ((size (i.1-c):ℕ):ℝ) by positivity)]
lemma run_node {Q:Cross L α β} (h:Whole Q)(p:Site L): ∃ B:ℝ,0≤B∧ ∀ i, Charge 1 (node p Q i) B := by
  obtain ⟨u,C,hu,h⟩:=h
  let b:=Fintype.card β*C
  refine ⟨max 0 b,le_max_left ..,fun i=>(node0 h p i).mono (fun _=> zero_le_one) (fun _=>Real.one_le_exp (by positivity)) (le_max_right ..)⟩

def belly (p:Site L) (Q: Cross L α β)(V:Rooted E α r) := revolve V (fun _=> node p Q)
lemma belly_mood (p:Site L) (h:Whole Q)(hp:Tidy V): Tidy (belly p Q V) := by
  obtain ⟨B,hB,H⟩:=run_node h p
  refine revolve_s (node p Q) hp (Ink.pens (bulb_price (V:=V) (w:=1) (v:=1) (C:=∑' i,‖V i‖) (p:=fun _:Fin r=>B) ?_ (fun _=> hB) ?_) (fun i=> fineBro (show (1:Cover×β→ℝ)≤1 from le_rfl) i.2)) -- args
  · simp only [show brocade (1:Cover×α→ℝ)=(1:Beads α r→ℝ) from funext fun x=>by simp [brocade]]; exact hp.pens.priced
  intro i j; simpa using H j
lemma belly_sound {Q:Cross L α β}(x:E→L[ℝ] ℝ)(p:Site L)(h:Whole Q)(hp:Tidy V): x∘belly p Q V=belly p Q (x∘V) := by
  obtain ⟨B,hB,H⟩:=run_node h p
  refine revolve_eval (Ink.pens (bulb_price (V:=V) (w:=1) (v:=1) (C:=∑' i,‖V i‖) (p:=fun _:Fin r=>B) ?_ (fun _=> hB) ?_) (fun i=>fineBro (show (1:Cover×β→ℝ)≤1 from le_rfl) i.2)) x
  · rw [show brocade (1:Cover×α→ℝ)=(1:Beads α r→ℝ) from funext fun x=>by simp [brocade]]; exact hp.pens.priced
  intro i j; simpa using H j

variable [Fintype α]
lemma node_period (g: Ratio c f) (p:Site g.count) {Q:Cross g.count α β}(hp:Whole Q)(b:Site c)(i:Cover×α)(f':PAC β c): pursed (node p Q) (fun x=> f' (b+wrap c x.1,x.2)) i=
    (installed g Q *ᵥ f') (g.assemble (b,p)+wrap f i.1,i.2) := by
  obtain ⟨m,C,h,hE⟩:=hp
  let c':=carry p i.1
  let e: Cover×β ≃ Cover×β:= Equiv.prodCongr (Equiv.addRight c') (Equiv.refl _)
  let a:= g.assemble (b,p)+wrap f i.1
  have ht : (installed g Q *ᵥ f') (a,i.2)=(Q.acts c *ᵥ f') (splitCo g α (a,i.2)):= rfl
  have he : splitCo g α (a,i.2) = ((b+wrap c c'),(arrives p i.1, i.2)) := by
    unfold a; simp only [split_co,moves_parent,g.assemble_parent,moves_residue,g.assemble_res]; rfl
  unfold pursed; rw [← e.tsum_eq,ht,he,row_expand hE h.le]; apply tsum_congr; rintro ⟨x,y⟩
  change Q (arrives p i.1,i.2) y (x+c'-c')* f' (b+wrap c (x+c'),y)=_
  rw [add_sub_cancel_right,map_add, add_comm _ (wrap c c'),← add_assoc]
lemma belly_period (g:Ratio c f) (p:Site g.count) {Q:Cross g.count α β}(h:Whole Q){V: Rooted ℝ α r}(he:Tidy V) (b:Site c)(Z:Fin r→ PAC β c): stitch (belly p Q V) c b Z=stitch V f (g.assemble (b,p)) (fun i=>installed g Q*ᵥ Z i) := by
  obtain ⟨B,hB,H⟩:=run_node h p
  have hh :∀ i,Charge (1:Cover×β→ℝ) (node p Q i) (B*(1:Cover×α→ℝ) i) :=fun i=> by simpa using H i
  let f i (v:Cover×β):= Z i (b+wrap c v.1,v.2)
  have hp:= divulge (P:=fun _=>node p Q) (show Quire.Ink (brocade (1:Cover×α→ℝ)) V (∑' i,‖V i‖) by rw [show brocade (1:Cover×α→ℝ)=(1:Beads α r→ℝ) from funext fun _=>by simp [brocade]]; exact he.pens.priced) (p:=fun _=> B) (fun _=>hh) (fun _=>hB) (le_refl _) f (fun i=> ‖Z i‖) (fun _=>norm_nonneg _) (fun i v=> by rw [Pi.one_apply,mul_one]; exact norm_le_pi_norm (Z i) _)
  unfold f at hp; rw [show (fun i=> pursed (node p Q) (fun x:Cover×β=> Z i (b+wrap c x.1,x.2))) = _ from funext fun i=>funext fun x=> node_period g p h b x (Z i)] at hp
  rw [stitch_apply ((belly_mood p h he).pens.of_norm),stitch_apply (he.pens.of_norm)]; exact hp
end YM.RG08.Vale
