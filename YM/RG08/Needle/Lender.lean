import YM.RG08.Needle.Dane
/-!
# Normalized columns as linear maps, usual factorials via the label probes

Finite LAP expansions, no bare N→∞ implicit. PowerSeries records the
dependence on the LEVEL's own coupling. Commutation of maps with Taylor
cutoffs checked before rearranging.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {I E α β :Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]{G:Gauge}{L c f p: Side}{w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}
variable {F:Labels.Frame G d} {P U:Screed E α}
def adapt (U:Screed E α)(p : PowerSeries ℝ)(n:ℕ) := ∑ i ∈ range (n+1), coeff i p • fem i U
def fund (U:Screed E α)(p : PowerSeries ℝ)(e:ℕ) := adapt U p e e
lemma stranded (U:Screed E α)(p:PowerSeries ℝ)(n j:ℕ) (h:j≤n) : (fund U p j)= adapt U p n j := by
  unfold fund adapt; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_subset (range_mono (Nat.succ_le_succ h)) fun i hi hb=> by
    rw [Pi.smul_apply,show fem i U j=0 from funext fun r=> if_neg (fun hk=>hb (mem_range.mpr (Nat.lt_succ_of_le hk))),smul_zero]
-- this detects across ANY origin/banner, no identifying cuts or linear dependencies of local stencils
lemma mugged (e: E→L[ℝ] ℝ) (a : Beads α r)(i:ℕ)(h:PowerSeries ℝ)(P:Screed E α):
    e (fund P h i r a)=coeff i (h*PowerSeries.mk (fun j=> e (P j r a))) := by
  unfold fund adapt; simp_rw [Finset.sum_apply,map_sum,Pi.smul_apply,map_smul, smul_eq_mul]
  rw [PowerSeries.coeff_mul]; symm
  have hp : (∑ x∈antidiagonal i, coeff x.1 h * coeff x.2 (PowerSeries.mk (fun j=>e (P j r a))))=∑ j∈range (i+1), coeff j h * e (P (i-j) r a):= by
    simp_rw [coeff_mk]; apply sum_nbij' Prod.fst (fun p=>(p,i-p))
    · intro j hj; exact mem_range.mpr (by have ht := mem_antidiagonal.mp hj; omega)
    · intro j hj; exact mem_antidiagonal.mpr (by have ht:=mem_range.mp hj; omega)
    · rintro ⟨x,y⟩ h; change (_,_)=(x,y); rw [show i-x=y from (by have he : x+y=i:= mem_antidiagonal.mp h; omega)]
    · intro _ _; rfl
    intro j hj; rw [show i-j.1=j.2 from (by have he:=mem_antidiagonal.mp hj; omega)]
  exact hp.trans (sum_congr rfl fun b hb=> by rw [footing (mem_range_succ_iff.mp hb)])
variable [Fintype I] [DecidableEq I] [Fintype β]
abbrev Native (I:Type) := I → PowerSeries ℝ
abbrev Session (I:Type) := Matrix I I (PowerSeries ℝ)

def edgeBook (f:I→ Screed E α)(v:Native I): Screed E α:=∑ i,fund (f i) (v i)
def bureau (f:I→ Screed E α)(M:Session I)(i:I) : Screed E α:= edgeBook f (fun j=> M j i)
lemma edge_marks (f:I→ Screed E α)(x: Native I)(i: ℕ) : Same (edgeBook f x) (∑ j,adapt (f j) (x j) i) i := fun j hj=> by unfold edgeBook; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun k _=>stranded _ _ _ _ hj
lemma mugs_tot (e: E→L[ℝ] ℝ) (a:Beads α r) (P : I → Screed E α) (v : Native I):
    PowerSeries.mk (fun j=>e (edgeBook P v j r a))=∑ i,v i*PowerSeries.mk (fun j=> e (P i j r a)) := by
  ext i; unfold edgeBook; simp_rw [Finset.sum_apply,map_sum,mugged]; rw [coeff_mk]
lemma planks (e:E→L[ℝ] ℝ) (a:Beads α r) (P:I→Screed E α)(M:Session I)(i:I):
    PowerSeries.mk (fun j=>e (bureau P M i j r a))=∑ k,M k i * PowerSeries.mk (fun j=>e (P k j r a)) := mugs_tot ..
variable {V W:BoardU D R G}
lemma speak_basis (h: ∀ r (p:Exam D)(a: Beads (Loc G 1) r), PowerSeries.mk (fun j=> plug p R (V j r a))= PowerSeries.mk (fun j=> plug p R (W j r a))) : V=W := by
  funext i r; apply envelope_ext; intro p; funext b; simpa only [PowerSeries.coeff_mk] using! congr_arg (PowerSeries.coeff (R:=ℝ) i) (h r p b)
lemma telephone (F:I→ BoardU D R G)(M:Session I)(v : Native I): edgeBook (bureau F M) v=edgeBook F (M*ᵥ v) := by
  apply speak_basis; intro r p a
  rw [mugs_tot,mugs_tot]; simp_rw [planks]
  let S i:= PowerSeries.mk (fun j=>plug p R (F i j r a)); simp_rw [Finset.mul_sum,Matrix.mulVec,dotProduct,sum_mul]; rw [sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; refine Finset.sum_congr rfl fun j _=> ?_; ring
lemma bureau_acts (F:I→ BoardU D R G)(M N:Session I): bureau F (M*N)= bureau (bureau F M) N := by
  funext i; exact (telephone F M (fun j=> N j i)).symm
lemma bureau_one (F:I→ BoardU D R G): bureau F 1=F := by
  ext1 i; apply speak_basis; intro r p a; rw [planks]
  simp [Matrix.one_apply]
lemma bureau_add (F G':I→ Screed E α) (M:Session I): bureau (F+G') M=bureau F M+bureau G' M := by
  have hv (P: Screed E α)(Q:Screed E α)(z: PowerSeries ℝ): fund (P+Q) z=fund P z + fund Q z := by
    funext n r; unfold fund adapt; simp_rw [Pi.add_apply, Finset.sum_apply]; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; simp only [Pi.smul_apply, fem]; split <;> simp [smul_add]
  funext i; unfold bureau edgeBook; simp_rw [Pi.add_apply,hv,Finset.sum_add_distrib]
-- through route-level vector labels only
variable (P : Hol G)
lemma audit_funds (p:ℕ) (v : Native (Letter F)) (U: Letter F → BoardU D R G)(h : ∀ b, Marvel p (U b))(he:∀ b,Lank (U b)) (q: Letter F):
    PowerSeries.mk (fun j=> auditT P F (edgeBook U v) j q)= ∑ i,v i*PowerSeries.mk (fun j=> auditT P F (U i) j q) := by
  ext j
  rw [coeff_mk,_root_.map_sum]; have hv k:=edge_marks U v k
  rw [audit_init P F (hv j) j le_rfl,audit_sums]
  rotate_left
  · exact fun b _=> choir_array (τ:=p) _ fun i _=> choir_weight (stemmed (h b) (Nat.le_add_right ..)) _
  · exact fun b _=>lank_tbl fun i _=>lank_wt (lank_fee (he b) i) _ -- fix
  rw [Finset.sum_apply,Finset.sum_apply]; apply Finset.sum_congr rfl; intro b _
  let ψ i:= coeff i (v b); let W := PowerSeries.mk (fun j => auditT P F (U b) j q)
  have hh i : Marvel p (fem i (U b)):=stemmed (h b) (Nat.le_add_right ..)
  unfold adapt; rw [audit_sums P (fun i hi=> choir_weight (hh i) _) (fun i _=> lank_wt (lank_fee (he b) _) _),Finset.sum_apply,Finset.sum_apply] -- arg order
  simp_rw [audit_scale P _ (hh _) (lank_fee (he b) _),Pi.smul_apply, audit_fee]
  rw [PowerSeries.coeff_mul]; symm; apply sum_nbij' Prod.fst (fun p=>(p,j-p))
  · intro a ha; exact mem_range.mpr (by have he:=mem_antidiagonal.mp ha; omega)
  · intro a ha; exact mem_antidiagonal.mpr (by have he:=mem_range.mp ha; omega)
  · rintro ⟨x,y⟩ h; change (_,_)=(x,y); rw [show j-x=y from (by have he : x+y=j:=mem_antidiagonal.mp h; omega)]
  · intro _ _; rfl
  intro b hb; have ht:=mem_antidiagonal.mp hb; rw [coeff_mk, if_pos (by omega),show j-b.1=b.2 by omega]; rfl
end YM.RG08.Needle
