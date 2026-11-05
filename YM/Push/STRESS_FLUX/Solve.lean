import YM.Push.STRESS_FLUX.Scaling

/-!
Represent all cutoff tests by ONE exact quotient field per flux (then by
linear maps in `Charges`), at every separated configuration including ties,
using no kernel comparisons off `conf`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Annular
open Matching Table Work.A01 Function Filter Set MeasureTheory
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {i d D n : ℕ} {V : E4 → E4} {W : DiffPlan S} {H : S.RealSpin}

theorem total {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*} (A : ι → U →ₗ[ℂ] ℂ) (b : ι → ℂ)
    (h : ∀ n (s : Fin n → ι) (c : Fin n → ℂ), (∀ u, ∑ j, c j * A (s j) u = 0) → ∑ j, c j * b (s j) = 0) :
    ∃ u, ∀ j, A j u = b j := by
  classical
  let P := Finsupp.linearCombination ℂ A
  let Q := Finsupp.linearCombination ℂ b
  have he : P.ker ≤ Q.ker := by
    intro c hc
    let e := (Fintype.equivFin c.support).symm
    have ht (f : ι → ℂ) : ∑ j, c (e j) * f (e j) = ∑ j∈c.support, c j * f j :=
      (e.sum_comp fun j => c j * f j).trans (by simpa only [Finset.attach_eq_univ] using c.support.sum_attach (fun j => c j * f j))
    specialize h _ (fun j => e j) (fun j => c (e j))
    simp_rw [ht] at h
    change Q c = 0
    simp only [Q,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul]
    apply h
    intro u
    rw [ht (fun i => A i u)]
    simpa only [P,Finsupp.linearCombination_apply,Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.zero_apply] using LinearMap.congr_fun (show P c = 0 from hc) u
  let R := (P.ker.liftQ Q he).comp P.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g,hg⟩ := R.exists_extend
  obtain ⟨u,hu⟩ := (Module.evalEquiv ℂ U).surjective g
  have ht (c) : g (P c) = Q c := by
    rw [← P.quotKerEquivRange_apply_mk]
    change (g.comp P.range.subtype) (P.quotKerEquivRange _) = Q c
    rw [hg]; simp [R]
  refine ⟨u,fun j => ?_⟩
  have hc : g (A j) = b j := by simpa only [P,Q,Finsupp.linearCombination_single,one_smul] using ht (Finsupp.single j 1)
  rw [← hu] at hc; exact hc

def Represents (J : S.Stress) (B : S.Field d) (V : E4 → E4) (u : S.Field D) := ∀ (n : ℕ) (x : Points (n+1)) (q : Fin n → S.Tag) (χ : E4 → ℝ),
    x∈conf _ → Window x χ → about J χ V x q B = frontRead q x D u

lemma pick0 (hs : S.Hierarchy) (hd : W.Derivatives S) {v : Axis → Axis → L.Ref 4} (hJ : Conserved W H (draw S v)) (B : L.Ref d)
    (hv : Motion i V) (hS : Snip S v B D (3+i)) : ∃ u : S.Field D, ∀ (s : Audience L) (χ : E4 → ℝ), Window s.x χ →
    about (draw S v) χ V s.x (S.classTokens ∘ s.tags) (S.project d B) = frontRead (S.classTokens ∘ s.tags) s.x D u := by
  let J := draw S v
  choose ψ hψ using fun s : Audience L => exists_window s.x (generic_conf _ s.avoids)
  obtain ⟨u,hu⟩ := total (fun s : Audience L => S.injectFront s.tags s.x D) (fun s => about J (ψ s) V s.x (S.classTokens ∘ s.tags) (S.project d B))
    (fun m s c => shrunk hs hd hJ B hv hS s c _ (fun j => hψ (s j)))
  refine ⟨S.project _ u,fun s χ hw => ?_⟩
  have he := independent_about hs.smooth hd hJ V hv.smooth hv.rigid (generic_conf _ s.avoids) hw (hψ s) (S.classTokens ∘ s.tags) (S.project d B)
  have hc := S.at_project S hs.laws.toSymmetric (fun _ => le_rfl) (generic_conf _ s.avoids) (Fin.cons (α:=fun _ => L.Token) ⟨D,u⟩ s.tags)
  rw [Fin.comp_cons] at hc
  rw [he,front_eval]
  exact (hu s).symm.trans hc.symm

lemma pick (hs : S.Hierarchy) (hd : W.Derivatives S) {v : Axis → Axis → L.Ref 4} (hJ : Conserved W H (draw S v)) (B : L.Ref d)
    (hv : Motion i V) (hS : Snip S v B D (3+i)) : ∃ u : S.Field D, Represents (draw S v) (S.project d B) V u := by
  obtain ⟨u,hu⟩ := pick0 hs hd hJ B hv hS
  refine ⟨u,fun n x q χ hx hw => ?_⟩
  let J := draw S v
  let p := S.project d B
  have hc t (ht : t ∈ generic (n+1)) (hh : Window t χ) : about J χ V t q p = frontRead q t D u := by
    let a := -(t 0)
    have he : q = S.classTokens ∘ (Ward.expose ∘ q) := funext fun i => (Ward.sends_back (q i)).symm
    have hq := hu ⟨n,Points.across a t, by simp [a], Extraction.Order.nearGeneric a ht, Ward.expose ∘ q⟩ _ (shifted_window a hh)
    have := moved J V a hs.translations (generic_conf _ ht) hh q p
    change about J _ V _ _ p = _ at hq
    rw [← he, this, front_eval, homogeneous hs.translations (generic_conf _ ht)] at hq
    exact hq.trans (front_eval ..).symm
  rw [front_eval]
  let E := {t : Points (n+1) | t ∈ conf _ ∧ Window t χ}
  have he : IsOpen E := isOpen_iff_mem_nhds.mpr fun t ht => ((conf_open _).eventually_mem ht.1).and (window_open ht.2)
  apply Measure.eqOn_of_ae_eq (μ:=volume) (s:=E)
    (f:=fun t => about J χ V t q p) (g:=fun t => S.useAt S t (Fin.cons ⟨D,u⟩ q)) _
    (fun t ht => (flux_continuous J V (fun b => (hv.smooth b).continuous) hs.smooth ht.1 ht.2 q p).continuousWithinAt)
    ((S.class_smooth S hs.smooth _).continuousOn.mono fun _ ht => ht.1) (by rw [he.interior_eq]; exact subset_closure) (show x∈E from ⟨hx,hw⟩)
  filter_upwards [ae_restrict_of_ae (Extraction.almostGeneric _), ae_restrict_mem he.measurableSet] with t ht hh
  exact (hc t ht hh.2).trans (front_eval ..)
end YM.StressFlux.Annular
