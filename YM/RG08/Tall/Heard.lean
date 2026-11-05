import YM.RG08.Tall.Maker
/-!
# Taylor Word expense for coordinate resets
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Tall
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Scores.Pages Matrix Push.AbsoluteSums PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis Loom MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {I α E : Type} {G : Gauge} {D p n r k τ ε j h Λ l L : ℕ} {m c f : Side} {R : ℝ} {i : Site m}
variable {U V:BoardU D R G}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F H : Screed E α}
lemma cap_none : Fits τ (0:Screed E α) := fun i j h=> (h rfl).elim
lemma cap_plus (h : Fits τ F)(hp : Fits τ H): Fits τ (F+H) := fun i j hv=> by_contra (fun he=> hv (by rw [Pi.add_apply,Pi.add_apply,not_ne_iff.mp (mt (h i j) he),not_ne_iff.mp (mt (hp i j) he), add_zero]))
lemma cap_scale (h : Fits τ F)(a : ℝ) : Fits τ (a • F) := fun i j he=> h i j fun hz=>he (by rw [Pi.smul_apply,Pi.smul_apply,hz,smul_zero])
lemma Shore.pair {X Y:Screed ℝ (Loc G 1)} (h : Shore i τ X)(p : Shore i τ Y)(hX : ∀ a b,Tidy (X a b))(hY : ∀ a b,Tidy (Y a b)) : Shore i τ (X+Y) := vocalized (fun k=>by
    obtain ⟨B,hB⟩:= Shore.vessel h hX k; obtain ⟨A,hA⟩:= Shore.vessel p hY k
    exact ⟨B+A,fun j=> Cargo.added (hB j) (hA j) hX hY⟩)
lemma intones {X Y : Screed ℝ (Loc G 1)}{P : Config G m→ℝ}(h : Cargo i τ k n X P) (hp : Loom.strand τ k X=Loom.strand Λ j Y) : Cargo i Λ j n Y P := ⟨h.toShell,fun v hv=> (h.scores_at v hv).trans (by rw [hp])⟩

lemma choir_plus (h : Marvel τ U)(hp : Marvel τ V): Marvel τ (U+V) := by
  refine ⟨cap_plus h.cap hp.cap,fun i j=> (h.hem i j).plus (hp.hem i j), fun m φ i=>?_⟩
  let E(X:BoardU D R G)e r:=plug φ R∘X e r; have he:E (U+V)= E U+E V:= funext fun a=>funext fun b=> funext fun i=>map_add ..
  change Shore _ _ (E _); rw [he]; exact Shore.pair (h.wardrobe m φ i) (hp.wardrobe m φ i) (fun i j=> Tidy.map _ (h.hem i j)) (fun i j=> Tidy.map _ (hp.hem i j))
lemma choir_weight (h : Marvel τ U)(b : ℝ): Marvel τ (b • U) := by
  refine ⟨cap_scale h.cap b,fun i j=> (h.hem i j).scale b,fun m φ i=>?_⟩
  refine vocalized (fun k=>?_); let X (V : BoardU D R G) e r:=plug φ R∘V e r
  have hp : ∀ e r,Tidy (X U e r):= fun e r=> Tidy.map _ (h.hem e r)
  obtain ⟨W,hw⟩:= Shore.vessel (h.wardrobe m φ i) hp k
  have he: X (b•U)=b•X U:=funext fun i=> funext fun e=> funext fun j=>by simp [X]
  exact ⟨b • W,fun j=> ((show Cargo i τ j _ (X (b•U)) _ from he.symm ▸ Cargo.weight (hw j) hp b))⟩
lemma choir_none : Marvel τ (0: BoardU D R G) := ⟨cap_none,fun i j=> Tidy.zero ..,fun m φ i=>vocalized (fun k=> ⟨0,fun j=> intones (Cargo.blank (G:=G) i _ _ _) (X:=0) (τ:=τ) (k:=j) (by unfold Loom.strand; funext r; simp [funext_iff])⟩)⟩
lemma choir_array {U : I→BoardU D R G} (s : Finset I) (h : ∀ i∈s,Marvel τ (U i)): Marvel τ (∑ i∈s,U i) := by
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact choir_none
  | insert i s hi ih=>rw [sum_insert hi]; exact choir_plus (h _ (mem_insert_self ..)) (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma cap_room (h : Fits τ F)(hp : τ≤Λ) : Fits Λ F:= fun i j he=> (h i j he).trans (Nat.add_le_add_right hp i)
lemma wider (hp:Marvel τ U)(he:τ≤Λ) : Marvel Λ U := by
  obtain ⟨q,hq⟩ : ∃ q, Λ=τ+q:= Nat.exists_eq_add_of_le he
  subst Λ
  refine ⟨cap_room hp.cap he,hp.hem,fun m φ i=>?_⟩
  refine vocalized (fun k=>?_)
  let X j l:= plug φ R ∘ U j l; have hF : Fits τ X := Fits.echo hp.cap φ
  obtain ⟨W,hW⟩:= Shore.vessel (U:=X) (hp.wardrobe m φ i) (fun i j=> Tidy.map _ (hp.hem i j)) (k+q)
  let w (i:ℕ):= if q≤ i then W (i-q) else 0
  refine ⟨w,fun j=>?_⟩; unfold w; split
  next hv=>
    rw [← show k+q+τ=k+(τ+q) by omega]
    apply intones (hW (j-q)); funext r; unfold Loom.strand; split_ifs <;> first|omega| rfl| exact congr_arg (fun n=> X n r) (by omega)
  next hv=>
    refine intones (Cargo.blank (G:=G) i _ (τ+q) j) ?_
    unfold Loom.strand; funext r; split_ifs; swap; · rfl
    next hh=> exact (not_ne_iff.mp (mt (hF _ _) (by omega : ¬ r ≤ τ+(j+r-(τ+q))))).symm

-- add coupling monomial at fixed gate, *from* slot color τ at its input,
-- can reduce target capacity by that many (if also shifting target e index)
def fem (j : ℕ) (U : Screed E α) (k r : ℕ) : Rooted E α r := if j≤k then U (k-j) r else 0
lemma footing (h : j ≤ k) : fem j F k r=F (k-j) r := if_pos h
lemma elbow (h : Fits τ F)(hp : τ ≤ L+j): Fits L (fem j F) := by
  intro e r he
  by_cases hh:j≤e
  · rw [footing hh] at he; have hu:=h _ _ he; omega
  unfold fem at he; rw [if_neg hh] at he; contradiction
lemma stemmed (h : Marvel τ U)(hp : τ ≤ L+j): Marvel L (fem j U) := by
  refine ⟨elbow h.cap hp,fun a b=>?_,fun m φ i=>?_⟩
  · unfold fem; split; apply h.hem; exact Tidy.zero ..
  refine vocalized (fun k=>?_)
  have hm:= wider h hp; let X j l := plug φ R∘U j l
  obtain ⟨W,hW⟩:= Shore.vessel (hm.wardrobe m φ i) (U:=X) (fun e r=> Tidy.map _ (h.hem e r)) k
  refine ⟨W,fun p=>?_⟩; refine ⟨(hW p).toShell,fun a ha=>?_⟩
  rw [(hW p).scores_at a (by omega)]; congr 1; unfold Loom.strand; split_ifs with he hv
  · dsimp only; rw [footing (show j ≤ p+a-L by omega)]
    exact congr_arg (fun n=>plug φ R ∘ U n a) (by omega)
  · omega
  · apply Eq.symm; dsimp only; have H : ¬ j ≤ p+a-L := by omega
    unfold fem; rw [if_neg H]; ext; simp
  rfl
end YM.RG08.Tall
