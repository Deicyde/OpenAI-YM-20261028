import YM.RG08.Vale.Wreathe
/-!
# Gain through all order-diagonal deterministic blocks incl marks
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {S ξ Υ R A B z:ℝ} {d D m r h:ℕ} {L c f:Side} {V:EnvelopeU D R G r}
variable {X:Cross L (Loc G 1) (Loc G 1)} {F K : Cover × Loc G 1 → ℝ} {w : Site L}
lemma halo_tid (hx:Odd L.val)(hp:1/2≤R)(hP:Tidy V)(he:Whole X): Tidy (halo w V X) := belly_mood _ he ⟨rays_print hP.pens hp hx w,fun i j=> congr_arg (fun z=>readdress z w) (hP.woven i j)⟩
lemma whirl_cost (hp: 1/2≤R) (hA:1≤A)(hw:1≤K) (hz:d+1≤D)(r:ℕ): ∃ C:ℝ,1≤C ∧
    ∀ (L:Side)(Q:Cross L (Loc G 1) (Loc G 1))(hy:Odd L.val),TakesP Q F K d A → ∀ p (U:EnvelopeU D R G r)(E:ℝ),
    Quire.Ink (brocade F) U E→∀ x v,Quire.Ink (fun i:_×Beads (Loc G 1) r=>brocade K i.2) (whirl hy hp hz p Q U x v) (C*height L (burden x v)*E) := by
  obtain ⟨C,hC,H⟩:= savings (α:=Loc G 1) (p:=F) hw d hA
  obtain ⟨M,hM,hZ⟩:= chest_income d (d+1) D rfl hz R hp
  refine ⟨C^r*M,one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) hM,fun L Q hy he p U E hu x v=>?_⟩
  have hv (i y): Charge K (partsP d (v i) p Q y) (C*height L ((v i).val+1)* F y) := by
    unfold partsP; split_ifs with h
    · rw [h]; exact (H L Q he _ _).2
    exact (H L Q he _ _).1 _ (by have ht:= (v i).isLt; omega)
  let W b:= (U b).comp (chest hy hp hz p x)
  let A:=height L x.val
  have hx : 0≤ M*A:= mul_nonneg (zero_le_one.trans hM) (height_p ..).le
  have hg (b): ‖W b‖≤(M*A)*‖U b‖ := (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul_of_nonneg_left (hZ _ _ _ _) (norm_nonneg _)).trans_eq (mul_comm ..))
  have hh : Quire.Ink (brocade F) W (M*A*E):= budget_mono (budget_scale hx hu) (fun p=>mul_nonneg ((fineBro he.first p).trans' zero_le_one) (norm_nonneg _)) (fun i=> (mul_le_mul_of_nonneg_left (hg i) ((fineBro he.first i).trans' zero_le_one)).trans_eq (mul_left_comm ..))
  apply Ink.raise (bulb_price (p:=fun i=> C*height L ((v i).val+1)) hh (fun i=> mul_nonneg (zero_le_one.trans hC) (height_p ..).le) hv)
  unfold burden A height; simp only [Finset.prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,prod_pow_eq_pow_sum]; exact le_of_eq (by ring)
lemma present_gain (he:1/2≤R)(hx:1≤A)(hp:1≤K)(hN:d+1≤D)(r:ℕ):∃ C:ℝ,1≤C∧
    ∀ (L:Side)(Q:Cross L (Loc G 1) (Loc G 1)),Odd L.val→TakesP Q F K d A→∀ (p:Site L)(U:EnvelopeU D R G r)(B:ℝ),
      Polished U→Abates U (d+1)→Quire.Ink (brocade F) U B→Quire.Ink (brocade K) (halo p U Q) (C*height L (d+1)*B) := by
  obtain ⟨C,hC,H⟩:= whirl_cost (F:=F) he hx hp hN r
  let w:= (((d+2:ℕ):ℝ)*↑(Fintype.card (Fin r→Fin (d+1))))*C
  have hw: 1≤ w := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_cast; omega) (by exact_mod_cast Fintype.card_pos)) hC
  refine ⟨_,hw,fun L Q ho h p U B hu hh hU=>?_⟩
  have hs x v:=H L Q ho h p U B hU x v; have hv := fun x v=> (hs x v).pens (fun i=>fineBro hp _)
  rw [whirl_pen ho he hN hv]
  have hz: 0≤brocade K (r:=r) := fun i=> zero_le_one.trans (fineBro hp i)
  apply Ink.raise (Ink.additions (f:=fun x=>∑ z, vanish ho he hN p Q U x z) (fun x _=> Ink.additions (v:=brocade K) (g:=fun _=> C*height L (d+1)*B) (s:=univ) ?_ hz) hz)
  swap
  · intro j _; by_cases hb : burden x j<d+1
    · rw [whirled ho he hN hh hu _ _ _ _ (Nat.le_of_lt_succ hb) (hv x j)]
      exact (Ink.none ..).raise (mul_nonneg (mul_nonneg (zero_le_one.trans hC) (height_p ..).le) hU.nonneg)
    apply Ink.raise (show Quire.Ink _ _ _ from budget_projection (g:=whirl ho he hN p Q U x j) (brocade K) (fun i=>zero_lt_one.trans_le (fineBro hp _)) (hs x j))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (height_one L (Nat.le_of_not_gt hb)) (zero_le_one.trans hC)) hU.nonneg
  simp only [w,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.add_assoc]; push_cast; linarith
-- Wreath on all components, part-output m

def aboard (m : ℕ)(Q:Cross L (Loc G 1) (Loc G 1))(V:EnvelopeU D R G r) :=
    ((L.val:ℝ)^m * ((Fintype.card (Site L):ℝ))⁻¹) • ∑ i:Site L, halo i V Q
lemma sailing (h:Odd L.val) (hx:1/2≤R)(hw:Tidy V)(he:Whole X): Tidy (aboard m X V) := (Tidy.additions (fun i _=>halo_tid h hx hw he)).scale _
lemma sail_gain_l (he:1/2≤R)(hw:1≤A)(hv:1≤K)(hd:d+1≤D)(r:ℕ) : ∃ C:ℝ,1≤C∧ ∀ (L:Side)(Q:Cross L (Loc G 1) (Loc G 1)),Odd L.val→ TakesP Q F K d A→∀ V: EnvelopeU D R G r,Polished V→ Abates V (d+1)→ ∀ (B:ℝ),Quire.Ink (brocade F) V B→ ∀ m:ℕ,
    Quire.Ink (brocade K) (aboard m Q V) (C*height L (d+1)*(L.val:ℝ)^m*B):= by
  obtain ⟨C,hC,H⟩:= present_gain (F:=F) he hw hv hd r; refine ⟨C,hC,fun L Q hL h V hV hs B hp m=>?_⟩
  apply Ink.raise (Ink.scale (Ink.additions (fun p _=>H L Q hL h p V B hV hs hp) (fun i=>zero_le_one.trans (fineBro hv _))) _)
  rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (by positivity)]; apply le_of_eq; field_simp
end YM.RG08.Vale
