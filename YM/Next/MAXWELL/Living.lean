import YM.Next.MAXWELL.Shelves


/-!
# Bundles in a low jet Rack

Use the Rack Noetherian, Reynolds, isolate *length-homogeneous*
factors. The spectator bound depends on G and the chosen jet shelf,
NOT on external word-length, or on total weight of the hidden read.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k w m n : ℕ}

def Host (G : Gauge) (d k : ℕ) := Submodule.span ℂ {p : WickPol G|∃ (n : ℕ) (r : Fin n → ℕ) (v : Fin n → WickPol G),
    (∀ i, Pure (r i) (v i) ∧ v i∈shellSector G d) ∧ k=∑ i,r i ∧ p=∏ i,v i}

private lemma distills_mul (p q : WickPol G) (k l : ℕ) (hp : Pure l p) :
    distill k (q*p)=if l≤k then distill (k-l) q * p else 0 := by
  classical
  let f (s : Slot G) := (1:ℕ)
  induction q using MvPolynomial.induction_on' with
  | add A B hA hB => rw [add_mul,map_add,hA,hB,map_add,add_mul]; split <;> simp
  | monomial s c =>
    let x := (MvPolynomial.monomial s c)
    change distill k (x*p)=_
    have hs : Pure (bulk s) x := isWeightedHomogeneous_monomial _ s c rfl
    have he : Pure (bulk s+l) (x*p) := hs.mul hp
    split_ifs with h
    · by_cases hv : k=bulk s+l
      · have ht : k-l=bulk s := by omega
        rw [(show distill k (x*p)=x*p from (hv ▸ he).weightedHomogeneousComponent_same),ht]; rw [(distilled_eq (bulk s) _).mp hs]
      have hw : k-l≠bulk s := by omega
      rw [show distill k (x*p)=0 from he.weightedHomogeneousComponent_ne k hv,show distill (k-l) (MvPolynomial.monomial s c)=0 from hs.weightedHomogeneousComponent_ne (k-l) hw]; rw [zero_mul]
    exact he.weightedHomogeneousComponent_ne k (by omega)

private lemma host_extend {d l : ℕ} {p q : WickPol G} (hp : p∈shellSector G d) (h : Pure l p) (hq : q ∈ Host G d k) :
    q*p∈Host G d (k+l) := by
  induction hq using Submodule.span_induction with
  | mem v H =>
    obtain ⟨n,r,v,hK,rfl,rfl⟩ := H
    refine Submodule.subset_span ⟨n+1,Fin.cons l r,Fin.cons (α:=fun _ => WickPol G) p v,
      fun i => Fin.cases ⟨h,hp⟩ hK i,?_,?_⟩
    · rw [Fin.sum_univ_succ]; exact add_comm ..
    rw [Fin.prod_univ_succ]; exact mul_comm ..
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add p q _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c p _ hv => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hv

private theorem finstock (G : Gauge) (j : ℕ) : IsNoetherianRing ↥(Rack G j) := by
  classical
  let V := {i : Slot G|i.1 ≤ j}
  let W := (a : Fin (j+1)) × Fin (legDim G a.val)
  let L : V → W := fun i => ⟨⟨i.val.1, Nat.lt_succ_of_le i.property⟩,i.val.2⟩
  haveI : Finite V := Finite.of_injective L (fun i j h => by
    let T : W → Slot G := fun p => ⟨p.1.val,p.2⟩; exact Subtype.ext (congr_arg T h))
  exact isNoetherianRing_of_ringEquiv _ (supportedEquivMvPolynomial (R:=ℂ) V).symm.toRingEquiv

theorem hosting (G : Gauge) (j : ℕ) : ∃ d, ∀ (k : ℕ) (p : WickPol G), p∈shelf G j → Pure k p → Painted p → p ∈ Host G d k := by
  classical
  let R := ↥(Rack G j)
  letI := finstock G j
  let V : Set R := {p|∃ k : ℕ,0< k ∧ Pure k p.val ∧ Painted p.val}
  let W : Submodule R R := Submodule.span R V
  obtain ⟨s,hs,h⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R:=R) V).mp (show W.FG from IsNoetherian.noetherian _)
  choose L hL using (fun p : R => cap_exists p.val)
  let d := s.sup L
  refine ⟨d,?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro p hp hK H
    by_cases ht : k=0
    · subst k; rw [bulk_zero p hK]
      have h : (1:WickPol G)∈ Host G d 0 := by
        apply Submodule.subset_span; exact ⟨0,fun _ => 0,fun _ => 1, isEmptyElim,by simp,by simp⟩
      nth_rw 1 [← mul_one (C _)]; rw [C_mul']; exact Submodule.smul_mem _ _ h
    let u : R := ⟨p,hp⟩
    let A : WickPol G →ₗ[ℂ] WickPol G := moyenne G |>.comp (distill k)
    have he (b : R) (hh : b∈ Submodule.span R (s:Set R)) (r : R) : A (r.val*b.val) ∈ Host G d k := by
      induction hh using Submodule.span_induction generalizing r with
      | mem b hh =>
        obtain ⟨l,ht,h',H⟩ := hs hh
        have hd : b.val∈shellSector G d := chain (Finset.le_sup (f:=L) hh) (sector.mpr ⟨hL b,H⟩)
        change moyenne G (distill k (_ * _)) ∈ _
        rw [distills_mul _ _ k l h']; split_ifs with hw
        · rw [paints_fact H]
          have hi : k-l < k := by omega
          have hy := gloss_shelf (fun i => (1:ℕ)) (k-l) r.val r.property
          let B := moyenne G (distill (k-l) r.val)
          have ha : k-l+l=k := by omega
          have hk : Pure (k-l) B := by
            rw [show B= distill (k-l) (moyenne G r.val) from (moyenne_gloss (fun _ => (1:ℕ)) _ _).symm]
            exact weightedHomogeneousComponent_isWeightedHomogeneous (k-l) _
          have hm := host_extend hd h' (ih (k-l) hi B (spaced_moy _ hy) hk (painted_moy _))
          rw [ha] at hm; exact hm
        rw [map_zero]; exact Submodule.zero_mem _
      | zero => simp [R]
      | add p q _ _ hx hy =>
        change A (r.val*(p.val+q.val))∈_; rw [mul_add,map_add]; exact Submodule.add_mem _ (hx r) (hy r)
      | smul c p _ hv => change A (r.val*(c.val*p.val)) ∈ _; rw [← mul_assoc]; exact hv (r*c)
    have ht := he u (h ▸ Submodule.subset_span (show u∈V from ⟨k,Nat.pos_of_ne_zero ht,hK,H⟩)) 1
    change moyenne G (distill k (1*p)) ∈ _ at ht; rwa [one_mul,(distilled_eq k p).mp hK,paints_self H] at ht
end YM.Maxwell.Free
