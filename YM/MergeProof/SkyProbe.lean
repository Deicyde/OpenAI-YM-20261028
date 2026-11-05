import YM.MergeProof.Canyon
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d p n N : ℕ}

variable (R : Weave G)
private lemma additive (I : Finset (Fin n)) (f : Fin n→Pre G) {r m : ℕ} (hf : ∀ i∈I,Continuous (f i))
    (h : ∀ i∈I,MicroAt (f i) r m) : MicroAt (∑ i∈I,f i) r m := by
  induction I using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact MicroAt.zero G r m
  | insert i s hi ih=>
    rw [Finset.sum_insert hi]
    let a := Finset.mem_insert_self i s
    have he : Continuous (∑ j∈s,f j) := by
      rw [funext (fun x : CoverConfig G=> Finset.sum_apply x s f)]
      exact continuous_finsetSum _ fun j hj=> hf j (Finset.mem_insert_of_mem hj)
    apply (h i a).add _ (hf i a) he
    exact ih (fun i hi=>hf i (Finset.mem_insert_of_mem hi)) (fun i hi=>h i (Finset.mem_insert_of_mem hi))

private lemma radius_uniform {B : Frame G d} {H : Hol G} (X : SectionData B) (he : Portfolio H X (R d)) :
    ∃ r m : ℕ,∀ x : Label G d,x∈Maxwell.equationIdeal G d → MicroAt (X.evaluate (B.coords (R d x))) r m := by
  let S := Maxwell.equationIdeal G d
  have hp {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (P : Submodule ℂ V) :
      Module.Free ℂ P ∧ Module.Finite ℂ P := ⟨inferInstance,inferInstance⟩
  haveI := (hp S).1; haveI := (hp S).2
  let E := Module.finBasis ℂ S
  let f : S →ₗ[ℂ] Pre G := ((X.eval_linear).mk' X.evaluate).comp
    (B.coords.toLinearMap.comp ((R d).toLinearMap.comp S.subtype))
  choose r m h using fun i=> (he.rank (E i).1 (E i).2).2
  let M := Finset.univ.sup m
  let A := Finset.univ.sup r
  refine ⟨A,M,fun x hx=>?_⟩
  let z : S := ⟨x,hx⟩
  change MicroAt (f z) _ _
  rw [← E.sum_repr z,map_sum]; simp_rw [map_smul]
  refine additive _ _ ?_ ?_
  · intro i _; apply Continuous.const_smul; exact (he.rank (E i).1 (E i).2).1
  intro i hi; exact ((h i).mono (Finset.le_sup (s:=Finset.univ) (f:=r) hi) (Finset.le_sup (s:=Finset.univ) (f:=m) hi)).scale (E.repr z i)
private lemma covers_radius (C : Family G) (w : ℕ) : ∃ r M : ℕ, ∀ k p : ℕ, M ≤ (C.side k p).val →
    ∀ x : Site (C.side k p),∀ y∈ (C.localSection w).footprint x,separation y x ≤ r := by
  classical
  let s := (C.localSection w).stencil
  choose r M hM using fun i:s=> place_size i.val
  refine ⟨Finset.univ.sup r,Finset.univ.sup M,fun k p hk x y hy=>?_⟩
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
  let j : s := ⟨i,hi⟩
  rw [separation,add_sub_cancel_right]
  exact ((hM j _ ((Finset.le_sup (f:=M) (Finset.mem_univ j)).trans hk)).2).trans (Finset.le_sup (f:=r) (Finset.mem_univ j))
private lemma featured_partition {P : Trial C} (i : Fin n) (q : Fin n→ C.book.Token) (x : Fin n→Site (C.side N p)) :
    featuring P q i N p x=moment (C.beta N p) (fun U=> P N p (x i) U * ∏ j∈Finset.univ.erase i,C.seen (q j) (x j) U) := by
  unfold featuring; congr 1; funext U
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_pos rfl]; congr 1
  exact Finset.prod_congr rfl fun b hb=> if_neg (Finset.ne_of_mem_erase hb)
open YM.MergeProof
theorem skyprobes (V:SectionData (C.labels.level d))(he:Portfolio C.params V (R d)) (δ:ℝ)(hδ:0 < δ)(n:ℕ)
    (w:Fin n →ℕ) : ∀ᶠ N:ℕ in atTop, ∀ p:ℕ, C.beta N p≠0 → ∀ a: Rowe C d, (C.factory d N p).terminal (a (N,p)) ∈ carrier C R d N p →
      ∀ q : Fin n→ C.book.Token, (∀ i,(q i).1=w i) → ∀ i : Fin n,∀ x,
      (∀ j, j ≠ i → δ ≤ C.S.a N * separation (x j) (x i)) →
      featuring (hallmarks V a) q i N p x=0 := by
  classical
  choose r M h using fun i=> covers_radius C (w i)
  let m := Finset.univ.sup r
  let K := Finset.univ.sup M
  obtain ⟨s,H,hH⟩ := radius_uniform R V he
  let g := s+m
  have ht : ∀ᶠ k : ℕ in atTop, C.S.a k * g < δ := by
    have hl := (C.S.shrinks.mul_const (g:ℝ)); rw [zero_mul] at hl
    exact hl.eventually (gt_mem_nhds hδ)
  filter_upwards [ht, lengths C.S K,lengths C.S H] with N hn hN hM p hβ a ha q hq i x hx
  let D := Finset.univ.erase i
  let T : Config G (C.side N p)→ ℂ := fun U=>∏ j∈D,C.seen (q j) (x j) U
  have hS : Envelope T := cont_envelope (continuous_finsetProd D fun j _=> C.continuousO ..)
  have he (j : Fin n) (hj : j∈D) y (hy : y∈ (C.localSection (q j).1).footprint (x j)) : y∈Outer s (x i) := by
    have hr := h j N p ((Finset.le_sup (f:=M) (Finset.mem_univ j)).trans (hN p)) (x j) y (by rwa [← hq])
    have hl : g < separation (x j) (x i) := by
      have hg : C.S.a N * g < C.S.a N * separation (x j) (x i) := hn.trans_le (hx j (Finset.ne_of_mem_erase hj))
      exact_mod_cast (lt_of_mul_lt_mul_left hg (C.S.a_pos N).le)
    have hy := Finset.le_sup (f:=r) (Finset.mem_univ j)
    have hp := separation_triangle (x j) y (x i); rw [separation_comm (x j) y] at hp
    change s < _; unfold g m at *; omega
  have hy : LocalOn (Outer s (x i)) T := fun P Q h=> Finset.prod_congr rfl fun j hj=>
    C.localO N p (q j).1 (q j).2 (x j) _ _ (agrees_mono h (fun _ hv=> he j hj _ hv))
  rw [featured_partition]; let X := C.factory d N p; obtain ⟨y,hy',h0⟩:= obtained R _ ha
  have hz : hallmarks V a N p (x i)= ((C.S.a N:ℂ)^d)⁻¹ • (V.evaluate ((C.labels.level d).coords (R d y)) ∘ expandAt (x i)):=by
      unfold hallmarks; unfold embedTo at h0; simp only [LinearEquiv.trans_apply] at h0; unfold initial; rw [(C.factory d N p).terminal.injective h0]
      let F:= C.labels.level d; let j:= C.path.levels.clock.threshold N; rw [show ∀ w:C.label d,F.scaled j⁻¹ (tied C d N w)=w from (tied C d N).left_inv]; rfl
  rw [hz]; exact ((hH y hy').scale (((C.S.a N:ℂ)^d)⁻¹)) (C.side N p) (hM p) (x i) (C.beta N p) hβ T hy hS
end YM.Push.Mark
