import YM.RG08.Vale.Gift
/-!
# Shifted polynomial ports with SHEAR in positioned tests
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
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {S ξ Υ R A B z:ℝ} {d D m j r h:ℕ} {L c f:Side} {V:EnvelopeU D R G r}
variable {X:Cross L (Loc G 1) (Loc G 1)} {F K : Cover × Loc G 1 → ℝ} {w : Site L}{T:Type}
lemma nodes_budget {α β:Type} [Fintype β] (A:Cross L α β) (h:Whole A)(n:ℕ):∃ C:ℝ,0≤C∧ ∀ p x, Charge (rug n) (node p A x) (C*rug n x) := by
  obtain ⟨σ,K,hσ,h⟩:=h
  let B := max K 0; have hb:0≤B:= le_max_right ..
  let c:=((σ⁻¹^n*n.factorial*Real.exp σ)*(Fintype.card β*B)); have hc:0≤c:= by unfold c; positivity
  refine ⟨c*(5:ℝ)^n,by positivity,fun p x=>?_⟩
  apply Ink.raise (nodePol (strip_mono h le_rfl (le_max_left K 0)) hσ p n x)
  rw [mul_pow,mul_comm _ c,←mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold rug dime Carrier.liftCost; gcongr; exact mul_le_of_le_one_left (by positivity) (Carrier.unitStep_le _)
-- summing true offset against a polynomial
lemma purse_line (K:Cross L (TypeFace 1) (TypeFace 1)) (p:Site L) (x : Potential G) (hw: Whole K)(hp:x∈ rangeLt (Axis→G.Color) d) (i: Fare G) :
    pursed (node p (painted G K)) (deckP x) i= scent i.2.2 (Carrier.applyLine K (Carrier.verdict x) (lift p+i.1) (heap i).2) := by
  classical
  obtain ⟨C,hC,H⟩:=v_purse hp
  have hx:Whole (painted G K) := by obtain ⟨u,T,h,h'⟩:=hw; exact ⟨u,T,h,paint_budget h'⟩
  obtain ⟨M,hM,hB⟩:=nodes_budget _ hx d; let U:= node p (painted G K); let b(v: Fare G):= U i v*deckP x v
  have hv: Summable b := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun j=>norm_nonneg (b j)) ?_ (budget_scale hC (hB p i)).2.1)
    intro j; unfold b; rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (H j) (norm_nonneg _)).trans_eq (by unfold rug U; ring)
  let A:=carry p i.1
  obtain ⟨σ,P,hP,hh⟩:=hw
  let y:= lift p+i.1
  have ht: Carrier.cellar L y=A:= by
    have hz:= Carrier.balance L y; have he:= carry_spec p i.1
    have hw : L.val • Carrier.cellar L y=L.val • A:= add_left_cancel (hz.symm.trans he); funext j; apply mul_left_cancel₀ (show (L.val:ℤ) ≠ 0 by positivity); simpa only [Pi.smul_apply,nsmul_eq_mul] using congr_fun hw j
  have Hc : ∑' j,b j=∑ a:Loc G 1,∑' j,b (j,a) := (Equiv.tsum_eq (Equiv.prodComm (Loc G 1) Cover) b).symm.trans (by simpa only [tsum_fintype] using! hv.prod_symm.tsum_prod)
  unfold pursed; change (∑' j,b j)=_
  rw [Hc,Fintype.sum_prod_type,← Equiv.sum_comp axisEquiv,Carrier.applyLine,map_sum]
  refine sum_congr rfl fun j _=> ?_; rw [Finset.sum_eq_single i.2.2]; swap; · intro c _ hc; simp [b,node,painted,YM.RG08.colored,hc.symm,U] -- fix
  swap; · simp
  let f:= Carrier.member K y (heap i).2 j
  obtain ⟨D,hD,hr⟩:= Carrier.royalties _ _ hp
  have hG:= (Carrier.stream_income (x:=A) (q:=f) hP (hh _ _) d hD (fun i'=>hr i' j)).2.1.of_norm
  rw [← (Equiv.addRight A).tsum_eq]; change _=scent _ (Carrier.stream f (Carrier.cellar L y) _)
  rw [ht,Carrier.stream,(scent _).map_tsum hG]; apply tsum_congr; intro v
  dsimp only [U,painted,b]; unfold node deckP; rw [map_smul]; change _=_; simp [heap, ← coord_map,add_comm, painted, A, f,Carrier.member, Carrier.verdict, y,Work.F08.arrives,YM.RG08.colored] -- fix
lemma translate_cost (K:Flight j m)(x:ℝ)(hx:0<x)(hj:4≤m)(hw:d≤j)(p:Site K.L)(b:Potential G)(hp:b∈ rangeLt (Axis→G.Color) d) : ∃ W∈ rangeLt (Axis→G.Color) d,
    W-height K.L d • b∈ rangeLt (Axis→G.Color) (d-1) ∧ pursed (node p (painted G (Carrier.linesOf K x))) (deckP b)=deckP W := by
  let Q:=Carrier.linesOf K x
  have hq:Whole Q := Carrier.stored K x hx hj
  obtain ⟨A,hA,h,B⟩:= Carrier.accepts_V x hx K hj hw b hp
  let g:=Place.seat (lift p); let W (x:E4) := A (x+g)
  have ht : W-A∈ rangeLt (Axis→G.Color) (d-1) := by
    suffices ∀ (j:ℕ), A∈ rangeLt (Axis→G.Color) j→ W-A∈rangeLt (Axis→G.Color) (j-1) from this _ hA
    intro j hj; cases j with
    | zero=> rw [rangeLt,Submodule.mem_bot] at hj; rw [show W=0 from funext fun i=> by unfold W; rw [hj]; rfl,hj]; simp
    | succ j=> exact Place.band_step hj g
  refine ⟨W, Place.band_shift hA g, show W-height K.L d • b∈ _ from ?_,?_⟩
  · rw [show W-height K.L d • b=W-A+(A-height K.L d • b) by abel]; exact Submodule.add_mem _ ht h
  funext i; rw [purse_line Q _ _ hq hp,B]; unfold deckP W g Carrier.verdict; rw [add_comm (lift p), Place.seat_add]
end YM.RG08.Vale
