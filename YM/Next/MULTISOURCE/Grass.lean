import YM.Next.MULTISOURCE.Germs

/-! all orders, finite-volume compact derivative bound; supports *not* uniform. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice Function Filter Finset MeasureTheory Work.G07 Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {G : Gauge} {n : Side}

abbrev Cl (G : Gauge) (n : Side) (k : ℕ) := (Fin k → Directions G n) × World G n

def mounting (F : World G n → V) : ∀ k : ℕ, Cl G n k → V
  | 0, a => F a.2
  | k+1, a => deriv (fun t : ℝ => mounting F k (Fin.tail a.1,dance (a.1 0) a.2 t)) 0

lemma pays_dance : ContDiff ℝ ∞ (fun v : Directions G n × World G n × ℝ => dance v.1 v.2.1 v.2.2) := by
  refine contDiff_pi.mpr fun i => ?_
  have ht₁ : ContDiff ℝ ∞ (fun v : Directions G n × World G n × ℝ => v.1 i) :=
    (contDiff_apply ℝ G.Color i).comp contDiff_fst
  have ht₂ : ContDiff ℝ ∞ (fun v : Directions G n × World G n × ℝ => v.2.2) := contDiff_snd.comp contDiff_snd
  have he : ContDiff ℝ ∞ (fun v : Directions G n × World G n × ℝ => G.mat (G.lieExp (v.2.2 • v.1 i))) :=
    (G.exp_jet.of_le le_top).comp (ht₂.smul ht₁)
  exact he.mul ((contDiff_apply ℝ G.Mat i).comp (contDiff_fst.comp contDiff_snd))

lemma climbs (F : World G n → V) (h : ContDiff ℝ ∞ F) (k : ℕ) : ContDiff ℝ ∞ (mounting F k) := by
  induction k with
  | zero => exact h.comp contDiff_snd
  | succ k ih =>
    let B (x : Cl G n (k+1) × ℝ) := (Fin.tail x.1.1,dance (x.1.1 0) x.1.2 x.2)
    have he : ContDiff ℝ ∞ B := by
      have ht i : ContDiff ℝ ∞ (fun x : Cl G n (k+1) × ℝ => x.1.1 i) :=
        (contDiff_apply ℝ (Directions G n) i).comp (contDiff_fst.comp contDiff_fst)
      have hp := pays_dance.comp (f:=fun x : Cl G n (k+1) × ℝ => (x.1.1 0, x.1.2,x.2))
        ((ht 0).prodMk ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
      have hZ : ContDiff ℝ ∞ (fun x : Cl G n (k+1) × ℝ => Fin.tail x.1.1) := contDiff_pi.mpr fun i => ht i.succ
      exact hZ.prodMk hp
    have hb : ContDiff ℝ ∞ (fun x : Cl G n (k+1) => fderiv ℝ (fun t => mounting F k (B (x,t))) 0) :=
      ContDiff.fderiv (g:=fun _ => (0:ℝ)) (f:=fun i t => mounting F k (B (i,t))) (ih.comp he) contDiff_const (by simp)
    exact hb.clm_apply contDiff_const

lemma climbed (F : World G n → V) (k : ℕ) (a : Fin k → Directions G n) (U : Config G n) :
    mounting F k (a,showU U)=leftDerivs (F ∘ showU) (List.ofFn a) U := by
  induction k generalizing U with
  | zero => simp [leftDerivs,mounting]
  | succ k ih =>
    rw [mounting,List.ofFn_succ,leftDerivs]; simp only; simp_rw [← dance_U,ih]; rfl

lemma attained (F : World G n → V) (h : ContDiff ℝ ∞ F) (k : ℕ) {ℓ : ℝ} (hl : 0 ≤ ℓ) :
    ∃ b : ℝ,LeftBound k (fun i => ‖i‖ ≤ ℓ) (fun _ => True) 1 b (F ∘ showU) := by
  have HT j : ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Config G n) (a : Fin j→ Directions G n), ‖a‖≤ℓ → ‖mounting F j (a,showU U)‖≤C := by
    let Z := Set.prod (Metric.closedBall (0 : Fin j→Directions G n) ℓ) (Set.range (showU (G:=G) (n:=n)))
    have hz : IsCompact Z := (isCompact_closedBall _ _).prod (isCompact_range visible)
    obtain ⟨C,H⟩ := (hz.image (climbs F h j).continuous.norm).bddAbove
    refine ⟨max 0 C,le_max_left ..,fun U a ha => (H ?_).trans (le_max_right ..)⟩
    exact ⟨(a,showU U), (show (a,showU U)∈ Z from ⟨(show a∈Metric.closedBall 0 ℓ from by simpa using ha), ⟨U,rfl⟩⟩), rfl⟩
  choose b hb hB using HT
  refine ⟨∑ i∈range (k+1),b i,fun l _ U => ?_,sum_nonneg (fun i _ => hb i),fun l hX ha i hi => ?_⟩
  · have he (V : Config G n) : leftDerivs (F ∘ showU) l V=mounting F l.length (l.get,showU V) :=
      by rw [climbed,List.ofFn_get]
    simp_rw [he]; exact (climbs F h _).comp (contDiff_const.prodMk ((exposed U).of_le le_top))
  have he := hB l.length i l.get ((pi_norm_le_iff_of_nonneg hl).mpr (fun j => ha _ (List.get_mem ..)))
  rw [climbed,List.ofFn_get] at he; rw [one_pow,mul_one]
  exact he.trans (single_le_sum (fun i _ => hb i) (mem_range.mpr (Nat.lt_succ_of_le hX)))

lemma enlarged {D : Directions G n → Prop} {k : ℕ} {F : Config G n→V} {a b : ℝ}
    (h : LeftBound k D (fun _ => True) 1 a F) (hx : a ≤ b) : LeftBound k D (fun _ => True) 1 b F :=
      ⟨h.smooth,h.nonneg.trans hx,fun l he hk i hi => (h.bound l he hk i hi).trans (by simpa)⟩
end YM.Multi.Step
