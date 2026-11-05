import YM.RG08.Vale.Leader
/-!
# Ward pricing for replacing tree pixels in order-diagonal terms
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
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][CompleteSpace E]
variable {G:Gauge} {p m c f L:Side}{v w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F:Labels.Frame G d}{T:SectionData F}
variable {X:Cross L (Loc G 1) (Loc G 1)} {V: EnvelopeU D R G r}{U : Rooted E (Loc G 1) j}

def twistP (U:Rooted E (Loc G 1) j)(r:ℕ) (i: Beads (Loc G 1) j × (Fin r→Lacing G j)) : E := Staffer.icing (Prod.snd ∘ i.1) i.2 • U i.1
def crock (U:Rooted E (Loc G 1) j)(r:ℕ):= sew (tub (twistP U r) (fun i=> sweets i.1 i.2))
lemma twist_paid (h:Pens U) (n:ℕ) : Pens (twistP U n) := by
  let p i:= ‖U i‖; have he:= Staffer.silkPens (F:=p) (r:=n) h
  have he' := he.norm; unfold Pens; convert he' using 1; ext i; simp [p,aglow,twistP,norm_smul,mul_comm]
lemma twist_fee (h:Quire.Lit U w A)(g:0≤v)(hx:r*v≤w): Quire.Ink (fun i:Beads (Loc G 1) j × (Fin r→Lacing G j) => ling v (sweets i.1 i.2)) (twistP U r) ((Real.exp (r*v)*silkSale G j r)*A) := by
  let p i:=‖U i‖; have hh : Glow p w A := by simpa only [Quire.Lit,Quire.Ink,p,Glow, Charge,norm_norm] using! h
  simpa [aglow,p,Quire.Ink,Charge,twistP,norm_smul,mul_left_comm,mul_comm,mul_assoc] using Staffer.silkBone hh g hx
lemma crock_tid (h:Pens U)(r) : Tidy (crock U r) := Tidy.sewn ((twist_paid h _).pours _)
lemma crock_map (h:Pens U)(k:E→L[ℝ] ℝ)(r:ℕ) : k ∘ crock U r=crock (k∘U) r := by unfold crock; rw [sew_map,Pens.echo_pool _ (twist_paid h _)]; congr 2; funext i; exact map_smul ..
lemma crock_bills (h:Quire.Lit U w A)(g:0≤v)(he:r*v≤w): Quire.Lit (crock U r) v ((Real.exp (r*v)*silkSale G j r)*A) := stitching (Ink.pour _ (twist_fee h g he) (ling_one g))
lemma crock_poly (u r j : ℕ) : ∃ C:ℝ, 0≤C ∧ ∀ (U:Rooted E (Loc G 1) j) (A:ℝ), Quire.Ink (mint (u*r)) U A→ Quire.Ink (mint u) (crock U r) (C*A) := by
  let P := ((r+1:ℕ):ℝ)^(u*r)*silkSale G j r
  have hp :0≤P:= mul_nonneg (by positivity) (silkSale_pos ..)
  refine ⟨P,hp,fun U A h=>?_⟩
  refine sewn_income _ (mint_pos _ _ _) (fun i s=> (Equiv.prod_comp s (fun k=> Vale.dime u (i k).1))) (Ink.pour _ ?_ (mint_one _ _ _))
  let b:=(Beads (Loc G 1) j); let L:= Fin r→ Lacing G j
  change Quire.Ink (fun i : b×L=> mint u (sweets i.1 i.2)) _ _
  apply Ink.sires_cost h _ (fun i : b×L=> icing (Prod.snd∘i.1) i.2) hp
  intro i
  let Q:= ((r+1:ℕ):ℝ)^(u*r); have hQ :0≤Q:= by unfold Q; positivity
  apply budget_finite (fun j=> mul_nonneg (mint_pos _ _ _ _) (norm_nonneg _)) -- fix type
  have he (v : L) : mint u (sweets i v) ≤ Q * mint (u*r) i := by
    have hG : (((girth (sweets i v)):ℝ)) ≤ r*((girth i:ℝ)+1) := by exact_mod_cast silk_thin i v
    have hv:=mint_pos (Loc G 1) j (u*r) i
    calc
      _ ≤ (1+(girth (sweets i v):ℝ))^(u*r) := Vale.greater_bill ..
      _ ≤ (((r+1:ℕ):ℝ)*(1+(girth i:ℝ)))^(u*r) := pow_le_pow_left₀ (by positivity) (by push_cast; linarith [show 0≤(girth i:ℝ) by positivity]) _
      _ ≤ _:= by rw [mul_pow]; exact mul_le_mul_of_nonneg_left (Vale.lower_bill i (u*r)) hQ
  calc
    _ ≤ Q*mint (u*r) i * ∑ v:L, ‖icing (Prod.snd∘i) v‖ := by rw [Finset.mul_sum]; exact Finset.sum_le_sum fun k _=> mul_le_mul_of_nonneg_right (he k) (norm_nonneg _)
    _ ≤ _:= by rw [show P*_=Q*mint (u*r) i * silkSale G j r from by unfold P Q; ring]; exact mul_le_mul_of_nonneg_left (ice_fee ..) (mul_nonneg hQ (mint_pos _ _ _ _))
lemma crock_hike {U:Shale (Loc G 1) j} (h:Pens U)(x:PAC (Candles G) m)(z: Site m):
    rootSong (crock U r) m z x=ink (fun t:ℝ=> rootSong U m z (dragged G m (t•x))) r := by
  unfold crock; rw [sew_diagonal (Pens.pours _ (twist_paid h _)),tallyOpus]; congr 2
  · exact funext fun i=> mul_comm ..
  exact h.of_norm
end YM.RG08.Needle
