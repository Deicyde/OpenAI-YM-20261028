import YM.RG08.Vale.Sculpt
/-!
# Slot-diagonal inversion budgets independent of block length/history. Before engineering
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c f L:Side} {R S A B:ℝ} {D d e j r n i k t:ℕ} {τ:ℕ} {F:Labels.Frame G d} {T:SectionData F}
variable {X:Cross L (Loc G 1) (Loc G 1)} {V:EnvelopeU D R G r}
lemma colorPay (K:Flight j n) (A:Cross K.L (TypeFace 1) (TypeFace 1)) {v B : ℝ} {u:ℕ} (h:PaysPath A v B u) : PaysPath (painted G A) v B u := ⟨h.odd,fun i hi=> by rw [paint_diffs]; exact paint_budget (h.offsets i hi)⟩
lemma canopy (n:ℕ)(h:S>0)(he:0≤A)(hu:1/2 ≤ R) (D r:ℕ):∃ C:ℝ,0≤C∧∀ (L:Side)(X:Cross L (Loc G 1) (Loc G 1)),Odd L.val → X.strip S A → ∀ (V:EnvelopeU D R G r)(B:ℝ), Quire.Ink (mint n) V B→∀ k,
    Quire.Ink (mint n) (aboard k X V) (C*(L.val:ℝ)^k*B) := by -- remove Z
  let K := (5:ℝ)^n*((S⁻¹^n*n.factorial*Real.exp S)*((Fintype.card (Loc G 1):ℝ)* A)); have hK:0≤K:=by unfold K; positivity
  refine ⟨K^r,pow_nonneg hK _,fun L X hO hX V B hB k=> ?_⟩
  have hv p t : Charge (rug n) (node p X t) (K*rug n t) := by
    apply Ink.raise (nodePol hX h p n t); unfold K
    rw [mul_comm ((5:ℝ)^n),mul_assoc, mul_pow, mul_comm,mul_assoc _ ((5:ℝ)^n)]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity); unfold rug dime Carrier.liftCost; gcongr; exact mul_le_of_le_one_left (by positivity) (Carrier.unitStep_le _)
  apply Ink.raise (Ink.scale (Ink.additions (s:=univ) (fun i _=> halo_ear hO hu rug_one rug_one i hK (hv i) (w:=rug n) hB) (zero_le_one.trans (fineBro rug_one))) _)
  rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (by positivity)]; apply le_of_eq; field_simp

variable (H: Hol G)(h:T.Sound H)(hh:Bid.pop T)(hx:1/2≤R)(hS:0<S)(hp:4≤n)(hj:4≤j)(hy:d+2 ≤ j)(hz:d+1≤D)
-- leading price before L, even though this is only one call per sweep. λ=L
include h hh hx hS hp hj hy hz
lemma leading_in (b v:Letter F)(hr:slot b=slot v) : ∃ A:ℝ,1≤A ∧ ∀ K:Flight j n, ‖leadingV H T (d.le_succ.trans hz) hx K S b v‖≤A * priceLit K b := by
  obtain ⟨σ,C,hσ,hC,hG⟩:=Carrier.priced S hS hj hp
  let n':= max d (d * slot v)
  let A:=startU T b (d.le_succ.trans hz) ((by norm_num : (0:ℝ)≤1/2).trans hx) 0 (slot b)
  obtain ⟨D', hD'⟩ := start_lank T b (d.le_succ.trans hz) ((by norm_num : (0:ℝ)≤1/2).trans hx) 0 (slot b) n'
  obtain ⟨R',hR',Hr⟩:= invest_price v R (slot b) D
  have hm (K:Flight j n)(E:ℝ) (he: Quire.Ink (mint n') (aboard d (painted G (Carrier.linesOf K S)) A) E): ‖leadingV H T (d.le_succ.trans hz) hx K S b v‖≤ R' * E := Hr _ E (he.shrink (mint_pos _ _ _) (mint_more (le_max_right ..))) H
  have hD :0≤ D':= hD'.nonneg
  by_cases hB:fee b=0
  · obtain ⟨P,hP,hR⟩:=canopy (G:=G) n' hσ hC.le hx D (slot b)
    refine ⟨1+R'*P*D',le_add_of_nonneg_right (by positivity),fun K=>?_⟩ -- maybe
    have ht := paint_budget (G:=G) (show (Carrier.linesOf K S).strip σ C from strip_mono (hG K [] (by simp)) le_rfl (by
        simp only [List.length_nil,add_zero,pow_one]; exact div_le_self hC.le (by exact_mod_cast K.L.property)))
    unfold priceLit; rw [hB,Nat.sub_zero]; apply (hm _ _ (hR K.L _ K.odd ht _ _ hD' d)).trans; nlinarith [show 0≤(K.L.val:ℝ)^d by positivity]
  obtain ⟨p,hb⟩ : ∃ p,fee b = p+1 := ⟨fee b-1,by omega⟩
  obtain ⟨f,hF,Hf⟩:= growthP (α:=Loc G 1) (β:=Loc G 1) σ C hσ hC.le n' p (by have := b.bill; unfold fee at hb; omega)
  obtain ⟨T',hT,H'⟩:=sail_gain_l (F:=rug n' (α:=Loc G 1)) hx hF (rug_one (α:=Loc G 1) (u:=n')) (by have he:fee b≤d:=b.bill; exact (by omega:p+1≤ D)) (slot b) -- fix params
  let U:=R'*T'*D'
  have hu : 0 ≤ U := by unfold U; positivity
  refine ⟨1+U,le_add_of_nonneg_right hu,fun K=>?_⟩
  let Q:=painted G (Carrier.linesOf K S)
  have hh: p+1=fee b:=hb.symm
  have hQ: PaysPath Q σ C p := colorPay K _ ⟨K.odd,fun i hi=> by
    have ht:= hG K i (by have he:fee b≤d:=b.bill; omega)
    simpa only [height,div_eq_mul_inv,inv_pow,Nat.add_comm] using ht ⟩
  apply le_trans (hm K _ (H' K.L Q K.odd (Hf K.L Q hQ) A (start_lank T b _ _ 0 (slot b)) (by rw [hh]; exact panning b H h _ _ 0 (slot b)) _ hD' d)) -- modify
  calc
    _ = U*priceLit K b := by unfold height priceLit U; rw [hh,inv_pow]; have hB : (K.L.val:ℝ)^d= (K.L.val:ℝ)^(d-fee b)*(K.L.val:ℝ)^(fee b) := by rw [← pow_add,Nat.sub_add_cancel (show fee b≤d from b.bill)]
                             rw [hB]; field_simp ; try ring
    _ ≤ (1+U)*priceLit K b:= mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by unfold priceLit; positivity)
end YM.RG08.Vale
