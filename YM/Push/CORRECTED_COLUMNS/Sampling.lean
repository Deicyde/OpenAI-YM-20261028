import YM.Next.EXTRACTION.Detector

/-!
# From positivity/detection gates at Maxwell to finite column choice

Upstream Maxwell pair separation remains physics/math input (reflected
Gram tests and polarization, ). Not inferred from
physical Wilson rank itself.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Sampling
open Table Function Cells Set Extraction Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) (d : ℕ)

/-- It suffices to know two-point detection on the actual free comparator
level. All separated pairs allowed, even nongeneric/tied-axis. An upstream
RFree argument could even use nondegeneracy of reflected singleton-word
smears. Uses arbitrary `d` (including low weights). -/
def PairSep : Prop :=
  let T := standard C
  ∀ x : T.Field d, (∀ (z : T.Field d) (q : Points 2), q ∈ conf _ →
    T.useAt T q ![⟨d,x⟩,⟨d,z⟩] = 0) → x=0

section
variable {L : Register G} {T : Table L}
/-- Real here means fixed by the actual anti-involution from the labels on
the reference space. Basis always contains the *unit*. -/
theorem frame (H : RealSpin T) (h : T.unit d ≠ 0) :
    ∃ (n : ℕ) (P : Module.Basis (Fin (n+1)) ℂ (T.Field d)),
      (∀ i, T.conj H d (P i) = P i) ∧ P 0 = T.unit d := by
  classical
  let j := T.conj H d
  let R : Set (T.Field d) := {x | j x=x}
  have hs : ⊤ ≤ Submodule.span ℂ R := by
    intro x _
    have hz : j (j x)=x := T.reflect_star H d x
    have ha : x+j x∈ Submodule.span ℂ R := Submodule.subset_span (show j (x+j x)=_ by rw [map_add,hz,add_comm])
    have hb : Complex.I • (x-j x)∈ Submodule.span ℂ R := Submodule.subset_span (show j _=_ by
      rw [j.map_smulₛₗ,map_sub,hz]; simp [smul_sub]; abel)
    have hg : x=(1/2:ℂ) • ((x+j x) + (-Complex.I) • (Complex.I • (x-j x))) := by
      rw [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,
        show x + j x + (x - j x) = (2:ℂ) • x by rw [two_smul]; abel,smul_smul, div_mul_cancel₀ _ (by norm_num), one_smul]
    rw [hg]; exact (Submodule.span ℂ R).smul_mem _ ((Submodule.span ℂ R).add_mem ha ((Submodule.span ℂ R).smul_mem _ hb))
  obtain ⟨s,hs',hPs,Hs,Hli⟩ := exists_linearIndepOn_id_extension
    ((linearIndepOn_singleton_iff ℂ).mpr h) (singleton_subset_iff.mpr (show T.unit d∈R from T.conj_unit ..))
  let P : Module.Basis s ℂ (T.Field d) := Module.Basis.mk (show LinearIndependent ℂ (Subtype.val : s → _) from
    Hli.linearIndependent_restrict) (by simpa using hs.trans (Submodule.span_le.mpr Hs))
  haveI : Finite s := Module.Finite.finite_basis P
  letI := Fintype.ofFinite s
  let si : s := ⟨T.unit d,hPs (mem_singleton _)⟩
  haveI : Nonempty s := ⟨si⟩
  let n := Fintype.card s-1
  have hn : Fintype.card s=n+1 := by dsimp [n]; have h := Fintype.card_pos (α:=s); omega
  let f : s ≃ Fin (n+1) := (Fintype.equivFin s).trans (finCongr hn)
  let i := f.trans (Equiv.swap (f si) 0)
  let B := P.reindex i
  have hw (x : s) : B (i x)= x.val := by simp [B,P]
  refine ⟨n,B,fun b => ?_,?_⟩
  · obtain ⟨x,rfl⟩ := i.surjective b; rw [hw]; exact hs' x.property
  rw [← show i si = 0 by simp [i], hw]
end

-- The matrix on this finite basis, as an exact array of true Maxwell readings.
def functional {ι : Type*} (D : SampleRow ι) {L : Register G} (S : Table L) (p : ι → S.Field d) :
    S.Field d →ₗ[ℂ] ℂ := Ward.here (Fin.cons ⟨d,(0:S.Field d)⟩ fun i => ⟨d,p (D.uses i)⟩) D.expected 0 d
lemma func {ι : Type*} (D : SampleRow ι) {L : Register G} (S : Table L) (p : ι → S.Field d) (x : S.Field d) :
    functional d D S p x = D.tests S p x := by
  rw [functional,Ward.takes]; unfold Ward.disc SampleRow.tests; congr 1
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

section
variable {I : Type*} [Fintype I]
private lemma generic_tests (P : Module.Basis I ℂ ((standard C).Field d)) (h : PairSep C d)
    (x : (standard C).Field d) (H : ∀ v : SampleRow I, v.tests (standard C) P x = 0) : x=0 := by
  let T := standard C
  apply h x
  intro z q hq
  let F (z : T.Field d) y := T.useAt T (n:=2) y ![⟨d,x⟩,⟨d,z⟩]
  have hv y (hy : y∈generic 2) i : F (P i) y=0 := by
    let w : SampleRow I := { extra := 1, cap := le_rfl, uses := fun _ => i, expected := y, probes := hy }
    have he : Fin.cons (α:=fun _ : Fin (1+1) => T.Tag) ⟨d,x⟩ (fun a : Fin 1 => ⟨d,P (w.uses a)⟩) =
        ![⟨d,x⟩,⟨d,P i⟩] := by funext j; fin_cases j <;> rfl
    unfold F; rw [← he]; exact H w
  have hg y (hy : y∈generic 2) : F z y=0 := by
    let f : T.Field d →ₗ[ℂ] ℂ := Ward.here (n:=2) (q := ![⟨d,x⟩,⟨d,x⟩]) y 1 d
    have hb u : f u=F u y := by
      unfold f; rw [Ward.takes]
      unfold F Ward.disc; congr 1; funext j; fin_cases j <;> simp
    rw [←hb,← P.sum_repr z,map_sum]; apply Finset.sum_eq_zero
    intro i _; rw [f.map_smul, hb,hv y hy,smul_zero]
  let V : Fin 2 → T.Tag := ![⟨d,x⟩,⟨d,z⟩]
  exact Dash.discl (conf_open 2) (F z) (fun _ => 0) ((T.class_smooth T (Maxwell.table_smooth C.labels) V).continuousOn)
    continuousOn_const (fun y hy => hg y hy.2) hq
end

theorem columns (S : Table C.book) (H : (standard C).RealSpin) (h : PairSep C d) :
    ∃ X : Columns C S d, ∀ x : (standard C).Field d, x≠0 →
      ∃ i, (X.row i).tests (standard C) X.basis x ≠ 0 := by
  classical
  let T := standard C
  obtain ⟨m,P,hP,hU⟩ := frame d H ((standard C).alive d (Maxwell.table_regular _))
  let f (v : SampleRow (Fin (m+1))) := LinearMap.toContinuousLinearMap (functional d v T P)
  obtain ⟨I,c,hc,hF⟩ := Next.Extract.finite_detectors (ContinuousLinearMap.id ℂ (T.Field d)) f fun x _ H =>
    generic_tests C d P h x (fun v => by rw [← func]; exact H v)
  let J := (Fintype.equivFin I).symm
  let g i := (J i).val
  have hx (x : T.Field d) (H : ∀ i, f (g i) x=0) : x=0 := by
    have hs : ∑ i∈I, ‖f i x‖=0 := Finset.sum_eq_zero fun i hi => by
      obtain ⟨w,hw⟩ := J.surjective (⟨i,hi⟩:I)
      rw [← show g w=i from congr_arg Subtype.val hw,H,norm_zero]
    have he := hF x
    simp only [ContinuousLinearMap.id_apply,sub_self,norm_zero,hs,add_zero] at he
    by_contra w; exact (mul_pos hc (norm_pos_iff.mpr w)).not_ge he
  let X : Columns C S d := ⟨m,H,P,hP,hU,Fintype.card I,g,fun x y hxy => ?_⟩
  · refine ⟨X,fun x hu => ?_⟩; by_contra! he
    apply hu (hx _ fun i => ?_); change functional d _ T P _=0; rw [func]; exact he i
  apply sub_eq_zero.mp (hx (x-y) fun i => ?_)
  rw [map_sub]; apply sub_eq_zero.mpr
  change functional d _ _ _ _=functional d _ _ _ _
  rw [func,func]; exact congr_fun hxy i
end YM.Push.Corrected.Sampling
