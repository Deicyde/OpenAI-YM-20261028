import YM.Next.MULTISOURCE.Render


/-!
# Fixed source-history tangents, no probes inserted at other steps
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Function Filter Finset Pack MeasureTheory Source Marker Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {P : Rep G n}
variable {d : ℕ} {F : Frame G d}

namespace BranchOne

variable (k : Coefficient F n) (C : SectionData F) (o : Site n)

def center (P : Rep G n) : Pulse G n := (k.exponentialEntry o C P, fun p U => Pack.collect P (fun i => k.forced i U) p)

private lemma as_pair (R : Census Unit) (x y : ℂ) (p : Poly R) :
    p.part R.quiet=x → p.part (R.fire ())=y → p=Poly.send R.quiet x+ Poly.send (R.fire ()) y := by
  intro hx hy; ext i
  by_cases he : i=R.quiet
  · subst i; rw [hx]; simp [Ne.symm (R.fire_hot ())]
  have he : i = R.fire () := by
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr (show i.val≠∅ from fun H => he (Subtype.ext H))
    cases a; apply Subtype.ext; change i.val = {()}; ext x; cases x; simp [ha]
  subst i; rw [hy]; simp [R.fire_hot]

lemma present {σ x Λ δ w a b : ℝ} (h : P.Lawful σ x Λ δ w) (he : k.remBound o P a b) :
    tangent P (center k C o P)= k.density o C P := by
  let R := Stock.census Unit
  let q := sendC R.quiet
  let j := sendC (R.fire ())
  funext U
  let A i := (P.activities.K i U:ℂ)
  let v i := k.forced i U
  let a i := q (A i) + j (v i)
  let W (i : Finset ℕ) : Poly R := if P.activities.admissible P.p U i then ∏ l∈i,a l else 0
  have hA : Summable A := by
    refine Complex.summable_ofReal.mpr ?_
    obtain ⟨B,hS,hB⟩ := Activities.K_total h.labels.boundK
    exact (hS.of_nonneg_of_le (fun i => norm_nonneg (P.activities.K i U)) (fun i => (hB i).2 U)).of_norm
  have hv : Summable v := by
    obtain ⟨x,y,-,-,-,-,-,f,hf,H⟩ := he
    exact (hf.2.1.of_nonneg_of_le (fun i => norm_nonneg (v i)) fun i => ((H i).2 _).trans (
      P.p.loMass _ _ (H i).1)).of_norm
  have hw : Summable a := ((hA.hasSum.map q q.continuous).add (hv.hasSum.map j j.continuous)).summable
  have hQ (i) : W i=q (P.activities.gasOccurrence P.p i U) + j (k.marked P i U) := by
    unfold Activities.gasOccurrence W Coefficient.marked
    split_ifs with h
    · apply as_pair; rw [quiet_of_prod,Complex.ofReal_prod]; unfold a
      · refine Finset.prod_congr rfl fun i _ => ?_
        change (Poly.send _ _ + Poly.send _ _).part _ = A i
        simp [Ne.symm (R.fire_hot ())]
      rw [first_of_prod]; unfold a
      change ∑ b∈ i,(Poly.send R.quiet (A b)+Poly.send (R.fire ()) (v b)).part _*
        ∏ x∈i.erase b,(Poly.send R.quiet (A x)+Poly.send (R.fire ()) (v x)).part _=_
      simp only [Poly.part_plus, Poly.part_send, R.fire_hot, Ne.symm (R.fire_hot ()),↓reduceIte, zero_add,add_zero]
      rfl
    simp
  have hW : Summable W := by
    obtain H := Complex.summable_ofReal.mpr ((Activities.gasSeries h.labels).summable U)
    have he := (Coefficient.marked_series h he).summable U
    rw [show W=_ from funext hQ]
    exact ((H.hasSum.map q q.continuous).add (he.hasSum.map j j.continuous)).summable
  have hb (p) : Pack.collect P a p=q (incumbent P U p)+j ((center k C o P).2 p U) := by
    unfold Pack.collect a
    have ht := Pack.access P A hA p; have hz := Pack.access P v hv p
    change _ = q (Pack.collect P A p) + j (Pack.collect P v p)
    unfold Pack.collect
    have hsum := ((ht.hasSum.map q q.continuous).add (hz.hasSum.map j j.continuous)).tsum_eq
    refine Eq.trans (tsum_congr (g:=_ + _) ?_) hsum
    intro i; simp only [Pi.add_apply, comp_apply]; split <;> simp
  have ht := Pack.regroup P U a hw hW
  have hx := congrArg (fun x : Poly R => x.part (R.fire ())) ht
  change (∑' i,W i).part _=_ at hx
  rw [Poly.share hW, Poly.part_sum] at hx
  simp_rw [hb,first_of_prod,hQ] at hx
  have hi (x y) : (q x+j y).part R.quiet=x := by change (Poly.send _ _ + Poly.send _ _).part _=_; simp [Ne.symm (R.fire_hot ())]
  have ho (x y) : (q x+j y).part (R.fire ())=y := by change (Poly.send _ _ + Poly.send _ _).part _=_; simp [R.fire_hot]
  simp_rw [hi,ho] at hx
  unfold Coefficient.density; rw [hx]; rfl

lemma costs {a b : ℝ} (L : Hol G) (h : k.Format o L P) (hh : k.remBound o P a b)
    (r t : ℝ) (hu : ‖k.x 0‖ ≤ r) (hv : Banked P.p 0 {o} (masked P.p.threshold (C.footprint o)
      (C.places (F.scaled (P.p.threshold)⁻¹ (F.core k.x)) o)) t) (ht : b+t ≤ r) (hp : b ≤ r) :
    Credit P.p 0 a {o} (center k C o P) r := by
  obtain ⟨x,y,hx,hy,hR,ha,⟨m,hm,Hm⟩, f,hf,H⟩ := hh
  let g j := k.maskedTerm P j
  let K := ofAddress P.activities
  let A q := Pack.collect P f q
  let Q U i := k.forced i U
  have he (i) := h.origin i
  refine ⟨singleton_nonempty _,le_rfl,ha, (norm_nonneg _).trans hu,
    ⟨k.x 0,_ + (fun U => ∑' i, g i U), ?_,by simp,hu, Banked.enlarge (Banked.add hv (b:=x) ?_ (singleton_nonempty _) le_rfl) ?_⟩, A, ?_⟩
  · funext i; exact add_assoc _ _ _
  · refine ⟨k.support,k.regular,m,fun i => ⟨by simp [h.origin],h.smooth i,(Hm i).1,?_
      ⟩,?_,fun _ => rfl⟩
    · intro j hj; exact (mem_singleton.mp hj) ▸ Hm i
    simp_rw [burn_zero]; exact hm
  · linarith
  have hs : Summable f := hf.2.1.of_nonneg_of_le (fun i => (H i).1) fun i => P.p.loMass _ _ (H i).1
  have hA q := Pack.access P f hs q
  constructor
  · let B i := burn P.p 0 (K i).zone
    have he : (∑ i : Pack n, burn P.p 0 i.zone * A i) = ∑' i, B i * f i := by
      unfold A Pack.collect; simp_rw [← tsum_mul_left]; rw [← Summable.tsum_finsetSum ?_]
      · apply tsum_congr; intro i; rw [sum_eq_single (K i)]
        · unfold B K; simp
        · intro j _ hj; rw [if_neg (show ¬ _ from Ne.symm hj),mul_zero]
        simp
      intro i hi; exact (hA i).mul_left _
    rw [he]; unfold B; simp_rw [burn_zero]; exact hf.2.2.trans (by gcongr; linarith)
  intro i
  refine ⟨gathers_legible P k.forced (fun j => ⟨h.borel j,h.invariant j,h.supported j,
    fun U hu => (h.forcing j U hu).1⟩) i,?_,tsum_nonneg (fun j => by split; exact (H _).1; exact le_rfl), fun U =>
    collects_bound P f _ hs (fun i => (H i).2 U) _⟩
  intro hH; rw [singleton_subset_iff]; by_contra hn
  apply hH; funext U; change Pack.collect P (Q U) i=0
  unfold Pack.collect; refine (tsum_congr (g:=fun _ : ℕ => (0:ℂ)) ?_).trans tsum_zero
  intro j; split_ifs with hz; swap; rfl
  change k.forced j U=0
  by_contra hi; apply hn; rw [← hz]; exact h.carried j fun H => hi (by rw [H]; rfl)
end BranchOne
end YM.Multi
