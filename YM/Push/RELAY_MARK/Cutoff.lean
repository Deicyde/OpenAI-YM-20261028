import YM.Next.EXTRACTION.Basis
import YM.Push.RELAY_MARK.Portfolio

/-!
# Physical cutoff mark at C.O (exact already from the section)

Use once the `Portfolio` for the C being constructed at RAuthors.
Same labels / F / path / β / factory terminal transformations. Need
no assumption of Makes to use the equation if just testing `β ≠ 0`;
of course Makes (with Portfolio) will be needed if claiming these as
calibrated fields! No requirement of even payment `dollar` for this
part; the result will work for arbitrary eligible arrays on every
refinement and covers the zero arity/vacuous queries and empty
spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d p n N : ℕ}

abbrev Weave (G : Gauge) := (d : ℕ) → (Label G d ≃ₗ[ℂ] Label G d)

variable (R : Weave G)

section AtStep

lemma positive_t (C : Family G) (N : ℕ) : 0 < C.path.levels.clock.threshold N := (C.path.levels.budget N).threshold_pos

def tied (C : Family G) (d N : ℕ) : C.label d ≃ₗ[ℂ] C.label d :=
    let F := C.labels.level d
    let t := C.path.levels.clock.threshold N
    { F.scaled t with
      invFun := F.scaled t⁻¹
      left_inv := fun v=>by
        have h := F.scaled_inv (inv_ne_zero (positive_t C N).ne') v
        simpa only [inv_inv] using! h
      right_inv := F.scaled_inv (positive_t C N).ne' }

/-- Full embedding to label C.d. E uses `a_N^(-d) t_N^(-l)` in J for each
homogeneous origin label with l curvature legs; in this version can instead
use just `a_N^(-d)` at this map, keeping all-slot cost on `tied`; it amounts
to choosing an equivalent **equation subspace** and parametrizing by the
linear Equiv. See budget uses. Input acts on `Label`, not a quotient. -/
def embedTo (C : Family G) (R : Weave G) (d N p : ℕ) : Label G d≃ₗ[ℂ]C.label d :=
    (((R d).trans ((C.labels.level d).coords)).trans (tied C d N)).trans (C.factory d N p).terminal

def carrier (C : Family G) (R : Weave G) (d N p : ℕ) :=
    (Maxwell.equationIdeal G d).map (embedTo C R d N p).toLinearMap

lemma obtained (u : C.label d) (v : u∈carrier C R d N p) :
    ∃ w : Label G d,w∈Maxwell.equationIdeal G d ∧ u=embedTo C R d N p w := by
  obtain ⟨y,hy,he⟩ := v; exact ⟨y,hy,he.symm⟩

lemma entry_mem (C : Family G) (R : Weave G) (d N p : ℕ) (x : Label G d)
    (he : x ∈ Maxwell.equationIdeal G d) : embedTo C R d N p x ∈ carrier C R d N p := ⟨x,he,rfl⟩

lemma calibrated_field (C : Family G) (R : Weave G) (d N p : ℕ) (o : Site (C.side N p))
    (x : Label G d) : C.O N p (embedTo C R d N p x) o =
    ((C.S.a N:ℂ)^d)⁻¹ • ((C.localSection d).evaluate ((C.labels.level d).coords (R d x)) ∘ expandAt o) := by
  simp only [Family.O,TransferData.cylinder,initial,embedTo,LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  let F := C.labels.level d
  let t := C.path.levels.clock.threshold N
  rw [show ∀ w:C.label d,F.scaled t⁻¹ ((tied C d N) w)=w from (tied C d N).left_inv]; rfl

lemma embed_signed (h : C.Makes) (he : Portfolio C.params (C.localSection d) (R d)) (hN : C.ref d ≤ N)
    (s : Signed) (x : Label G d) : embedTo C R d N p (theta s x)=(C.labels.level d).act s.ortho (embedTo C R d N p x) := by
  simp only [embedTo,LinearEquiv.trans_apply,he.inter]; unfold theta
  rw [← Frame.act_coords];
  rw [show ∀ w:C.label d, tied C d N ((C.labels.level d).act s.ortho w)= _ from fun w=> Frame.scaling _ _ s.ortho w,
    (h.calibrated d N p hN).orients]
  rfl

lemma embed_real (h : C.Makes) (he : Portfolio C.params (C.localSection d) (R d)) (hN : C.ref d ≤ N)
    (x : Label G d) : embedTo C R d N p (realBar x)=star (embedTo C R d N p x) := by
  let F := C.labels.level d
  simp only [embedTo,LinearEquiv.trans_apply,he.truly]
  have ht : ∀ v,F.coords (realBar v)=star (F.coords v) := fun v=>funext fun i=>by
    have hy := F.conj_basis (F.coords v) i; rw [LinearEquiv.symm_apply_apply] at hy; exact hy
  rw [ht];
  have hf (v : F.Coeff) : tied C d N (star v)=star (tied C d N v) := by
    funext i; change F.scaled _ (star v) i=star (F.scaled _ v i); simp [mul_comm]
  rw [hf,(h.calibrated d N p hN).realForm]
end AtStep

section Uniform

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

/-- Cutoff cylinders at arbitrary reference vectors in the kernel, including
whose reference coefficients move very fast. No restriction to a coordinate
lattice of placements avoiding the wrapping plane. -/
theorem marked_at_cutoff (he : Portfolio C.params (C.localSection d) (R d)) :
    ∃ r M : ℕ, ∀ N p, M ≤ (C.side N p).val → C.beta N p ≠ 0 →
      ∀ u:C.label d,u∈carrier C R d N p → ∀ o : Site (C.side N p),
      ∀ S : Config G (C.side N p)→ℂ,LocalOn (Outer r o) S → Envelope S →
       Integrable (fun P => (C.O N p u o) P*S P) (law G (C.side N p) (C.beta N p)) ∧
       moment (C.beta N p) (fun P => (C.O N p u o) P*S P)=0 := by
  obtain ⟨r,M,h⟩ := radius_uniform R _ he
  refine ⟨r,M,fun N p hm hb u hu o S hs hS=>⟨times_integrable (C.continuousO N p _ _ o) hS,?_⟩⟩
  obtain ⟨x,hx,rfl⟩ := obtained R u hu
  rw [calibrated_field]; exact ((h _ hx).scale (((C.S.a N:ℂ)^d)⁻¹)) (C.side N p) hm o (C.beta N p) hb S hs hS
end Uniform

section sep

-- NB all quantifiers: favorable separation from the one marked placement
-- suffices. Degrees may be fixed but all vectors can change at cutoffs.
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

lemma lengths (S : Schedule) (M : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, M ≤ (S.side N p).val := by
  refine (S.den_strict.tendsto_atTop.eventually_ge_atTop M).mono (fun N h p=>?_)
  exact le_trans h (le_mul_of_one_le_left (Nat.zero_le _) (S.period p).property)

private lemma featured_partition {P : Trial C} (i : Fin n) (q : Fin n→C.book.Token) (x : Fin n→Site (C.side N p)) :
    featuring P q i N p x=moment (C.beta N p) (fun U=> P N p (x i) U * ∏ j∈Finset.univ.erase i,C.seen (q j) (x j) U) := by
  unfold featuring; congr 1; funext U
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_pos rfl]; congr 1
  exact Finset.prod_congr rfl fun b hb=> if_neg (Finset.ne_of_mem_erase hb)

/-- True kernel equality uniformly before subsequence choice. Keep each slot.
No unselected diagonal limit asked for spectator or marked weights. Needs β≠0
at queried indices. -/
theorem all_probes (he : Portfolio C.params (C.localSection d) (R d)) (δ : ℝ) (hδ : 0<δ) (n : ℕ)
    (w : Fin n→ℕ) :
    ∀ᶠ N : ℕ in atTop,∀ p : ℕ, C.beta N p≠0 → ∀ a : Rowe C d,a (N,p)∈carrier C R d N p →
      ∀ q : Fin n→C.book.Token, (∀ i,(q i).1=w i) → ∀ i : Fin n,∀ x,
      (∀ j, j ≠ i → δ ≤ C.S.a N * separation (x j) (x i)) →
      featuring (upper C a) q i N p x=0 := by
  classical
  choose r M h using fun i=> covers_radius C (w i)
  let m := Finset.univ.sup r
  let K := Finset.univ.sup M
  obtain ⟨s,H,hH⟩ := marked_at_cutoff R he
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
  rw [featured_partition]; exact (hH N p (hM p) hβ (a (N,p)) ha (x i) _ hy hS).2

lemma sober_all (C : Family G) {d : ℕ} (a : Rowe C d) (f : Extraction.Order) : sober C (upper C a) f := by
  refine Eventually.of_forall fun p=> Eventually.of_forall fun j x=>?_
  have h := C.continuousO (f.mesh j) (f.per p) d (a (f.mesh j,f.per p)) x
  exact ⟨h.measurable,h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩

-- For the achieved portfolio mark even root discrepancy is zero.
lemma rent_zero (C : Family G) (f : Extraction.Order) : Bid.close C f (0 : Trial C) := by
  refine ⟨fun _ _=>0,tendsto_const_nhds,fun i k=> ⟨k,le_rfl,?_⟩⟩
  refine Eventually.of_forall fun p => (f.mesh.cofinal.eventually_ge_atTop k).mono ?_
  intro j hj
  refine ⟨hj,fun T ht hh x hx=>⟨Cells.Interior.constant _ _,?_⟩⟩
  have h0 := Next.Extract.root_smul T (C.beta (f.mesh j) (f.per p)) (G:=G) 0 (0:ℂ)
  simp only [smul_zero,norm_zero,zero_mul] at h0; exact h0.le
end sep
end YM.Push.Mark
