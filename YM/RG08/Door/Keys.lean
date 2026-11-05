import YM.RG08.Door.Kino
/-!
# Sector commodities. Contract within one slot stratum simultaneously all of that stratum.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {G:Gauge}{E e r s d τ D j t i k m :ℕ}{R C B A:ℝ}{F:Labels.Frame G d}{H:Hol G}
section y
variable {I J α Y : Type}{y v δ σ φ : I→ℝ}
structure Dig (y δ φ : I→ℝ) :Prop where
  asset: ∃ B,Weighed y B∧∀ i,‖φ i‖ ≤ B i *δ i
lemma Dig.rates (h: Dig y 1 φ) : Weighed y (fun i=> ‖φ i‖) := h.asset.choose_spec.1.mono (fun i=>norm_nonneg _) (fun i=>by simpa using h.asset.choose_spec.2 i)
lemma Dig.of_lease (h:Lease y δ φ σ) : Dig y δ (φ-σ):=⟨h.asset⟩
lemma Dig.of_rate (h: Weighed y (fun i=> ‖φ i‖)): Dig y 1 φ:=⟨_,h,fun i=>by simp⟩
lemma Dig.plus {p:I→ℝ}(h: Dig y δ φ)(hp:Dig y δ p)(he : Audience y): Dig y δ (φ+p) := by
  obtain ⟨A,hA,H⟩:= h.asset; obtain ⟨B,hB,HE⟩:= hp.asset; exact ⟨_,hA.plus hB he,fun i=> (norm_add_le ..).trans ((add_le_add (H _) (HE _)).trans_eq (add_mul ..).symm)⟩
lemma Dig.zero : Dig y δ 0 := ⟨0,Weighed.zero,fun i=>by simp⟩
lemma Dig.sums {φ:J→ I→ℝ} (s : Finset J) (he:Audience y)(h:∀ j∈s,Dig y δ (φ j)): Dig y δ (fun i=>∑ j∈s,φ j i) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Dig.zero
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=> h _ (mem_insert_of_mem hj)) he
lemma digs (H:Hol G){V:I→EnvelopeU D R G r}(ht : Tin y δ V v)(h:∀ i,0<v i)(hp:v≤1)(he:Weighed y (fun i=>(v i)⁻¹))(b:Letter F): Dig y δ (fun i=>invest H (V i) b) := by
  let k:= d*slot b; obtain ⟨C,hC,W⟩:= invest_price b R r D; obtain ⟨A,hA,U⟩:=ht.serves
  have hv: Weighed y (fun i=> Real.exp (v i)) := (Weighed.constant y (Real.exp_pos 1|>.le)).mono (fun _=>(Real.exp_pos _).le) (fun i=>Real.exp_monotone (hp i))
  have hh:=(Weighed.constant y hC).times (((((he.powers (k*r)).times (Weighed.constant y (Nat.cast_nonneg (k*r).factorial (α:=ℝ)))).times hv).times hA))
  exact ⟨_,hh,fun i=> (W _ _ (polish (U i) (h i) k) H).trans_eq (by simp only [Pi.mul_apply,mul_assoc])⟩
lemma dig_scale [NormedAddCommGroup Y][NormedSpace ℝ Y] {V:I→Rooted Y α r}(hp:Tin y 1 V v)(hx:Dig y δ φ): Tin y δ (fun i=> φ i • V i) v := by
  obtain ⟨B,hB,H⟩:=hp.serves; obtain ⟨A,hA,HX⟩:=hx.asset; refine ⟨_,hA.times hB,fun i=> Ink.raise (Ink.scale (H i) (φ i)) ?_⟩
  rw [Pi.one_apply,mul_one,Pi.mul_apply,mul_right_comm (A i)]; exact mul_le_mul_of_nonneg_right (HX _) (hB.positive i)
end y

section
variable {I Y α : Type} [NormedAddCommGroup Y] {q : Finset I}{V U:I→Y}
lemma tin_pool {Z: Type} {δ y v:Z→ℝ} {F:I→ Z→Rooted Y α r} (h:0≤δ)(hp: ∀ i∈q, Tin y δ (F i) v)(he:Audience y) : ∃ B,Weighed y B ∧ ∀ i∈q,∀ j,Quire.Lit (F i j) (v j) (B j*δ j) := by
  classical
  induction q using Finset.induction_on with
  | empty=> exact ⟨0,Weighed.zero,fun i h=>(notMem_empty _ h).elim⟩
  | insert i s hi ih=>
    obtain ⟨B,hB,H⟩:= ih (fun j hj=>hp _ (mem_insert_of_mem hj)); obtain ⟨A,hA,Hx⟩:= (hp i (mem_insert_self ..)).serves
    refine ⟨_,hA.plus hB he,fun k hk j=> ?_⟩
    rcases mem_insert.mp hk with h|hp
    · subst k; exact Ink.raise (Hx j) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hB.positive _)) (‹0≤δ› j))
    exact Ink.raise (H _ hp j) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hA.positive j)) (h j))
end
section
variable {I Y : Type} [AddCommGroup Y] [Module ℝ Y]
def footnote (b:I→Y)(R: Matrix I I ℝ)(p:I)(q:Finset I):Y:= ∑ i∈q,R i p • b i
lemma consume {l : Side} (f: Letter F→Y) (S : Session (Letter F))(hT:Flash l S)(i:Letter F) : footnote (fun j=> footnote f (diagonalSl (hot S 0)) j univ) (diagonalSl (hot S⁻¹ 0)) i univ=f i := by
  have h:= crown_slot hT
  let Q:= diagonalSl (hot S 0); let B:= diagonalSl (hot S⁻¹ 0)
  let Z: Letter F→Y:= fun j=> ∑ k:Letter F, Q k j • f k
  unfold footnote; change ∑ j:Letter F,B j i • Z j=f i; unfold Z
  simp_rw [Finset.smul_sum,smul_smul]; rw [sum_comm, Finset.sum_eq_single_of_mem i (mem_univ _)]; rotate_left
  · intro k hk hv; simp_rw [mul_comm _ (Q k _)]; rw [← Finset.sum_smul]; change (Q*B) k i • _=0; rw [show Q*B=_ from h,Matrix.one_apply,if_neg hv,zero_smul]
  simp_rw [mul_comm _ (Q i _)]; rw [← Finset.sum_smul]; change (Q*B) i i • _= _; rw [show Q*B=_ from h,Matrix.one_apply,if_pos rfl,one_smul]
lemma swap_coins {A : Loft F}{f:Letter F→Y}{b:Letter F}(he:slot (F:=F) b=i) : footnote f (diagonalSl A) b univ=footnote f (diagonalSl A) b (univ.filter (fun j=> slot j=i)) := by -- b binder
  symm; exact sum_subset (filter_subset ..) fun j hj ht=> by simp only [mem_filter,hj,true_and] at ht; simp only [diagonalSl, Matrix.of_apply,he,if_neg ht,zero_smul]
end
end YM.RG08.Door
