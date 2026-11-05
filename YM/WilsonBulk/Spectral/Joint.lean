import YM.Next.STATIONARY.Films.RankColor

/-!
# Getting joint pre-L **inverse strips** for use on strict events in bulk recursion.

Joint (fine, coarse frames). Do not choose a perturbed/interacting Hessian; the
quadratic symbol depends only on `frontR`, schedule, penalty. We use the gauge
completer of the one-loop calculation `postroom`, whose estimates on strips come
with a declared *pre-block* budget. (Use it with zero load -- even the fluctuation
spectrum only is a nontrivial application.) This does not require `FullPaths` or prior
purchase of favorable cubic or thermal taps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Work.F08 Precision Exterior Stationary Audience Matrix
open scoped Topology BigOperators ContDiff -- Classical issue?

variable {G : Gauge} {P : Patch} {c f : Side} {η Ω σ : ℝ}

private theorem blank_turns (S : StepData c f) : Turns (0 : Eye (Fin 0) (Acts G S.patch))
    (billZ S (0 : Corn (Co c (Fin 0))→L[ℝ] Bang G c f)) := by
  classical
  refine ⟨0,?_,?_⟩
  · intro p; simp only [LinearMap.zero_apply, billZ,ContinuousLinearMap.comp_apply,
      _root_.zero_apply, map_zero]; ext1 i; simp [axes]
  intro i q _ v; ext1 a; simp [tune]

lemma zero_spotlight (G : Gauge) (P : Patch) (w : ℝ) (h : w≤ 1) :
    Spotlight P (0 : Eye (Fin 0) (Acts G P)) w (Real.exp 4) := by
  refine ⟨h,⟨fun _ _ => rfl, fun _ _=>?_⟩,le_rfl, fun i => Fin.elim0 i⟩
  exact differentiableAt_const _

def regulatorF (G : Gauge) (P : Patch) := (CanonR (P:=P) (0 : Eye (Fin 0) (Acts G P)) false).tab

lemma regulator_turn (S : StepData c f) (hS : S.patch.Branches S.kernel G) (t : S.Choices) :
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S t (inch S.patch.L))))
      (regulatorF G S.patch) 0 := by
  have hx := (regulator_tour S t false _ (blank_turns S) hS (fun x => rfl)).tab
  dsimp only [cardM] at hx; rw [zero_hat S hS] at hx; exact hx

-- explicitly on every listed finite torus realizing the patch; no cost in period
lemma completion_choice (G : Gauge) (j : ℕ) (K : KernelChoices) (σ ε Ω : ℝ)
    (hσ : 0<σ) (hε : 0<ε) (hΩ : 0≤ Ω) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ σ ∧ 0 ≤ C ∧
      ∀ (P : Patch), P.J=j → P.Branches K G →
        ∀ (B : Bed) (p : Clip) (D : ℝ), B.metric.strip (inch P.L * σ) Ω →
          (∀ n, Floor B p n ε D) →
            Poster η (forceK G P (regulatorF G P) K.penalty B) ∧
            Freezer (slabW G P.L|>.dual) (slabW G P.L) (forceK G P (regulatorF G P) K.penalty B) η C := by
  obtain ⟨ζ,W,hζ,hζ',hW,H⟩ := amasses G
  let v:= min σ ζ; have hv:0<v:= lt_min hσ hζ
  have hg: v≤ σ := min_le_left ..
  have hu: v≤1 := (min_le_right σ ζ).trans (by linarith)
  obtain ⟨η,C,hη,hη',hC,h⟩:= post_cert G j K ε v Ω |tribute2 G j (Real.exp 4) W| hε hv hu hΩ (abs_nonneg _)
  refine ⟨η,C,hη,hη'.trans hg,hC,fun P hJ hP B p D he hF=> ?_⟩
  have he : B.metric.strip (inch P.L*v) Ω := fun i j => (he i j).mono (mul_le_mul_of_nonneg_left hg (inch_pos _).le) le_rfl
  have hZ:= conquer hP hv (zero_spotlight G P v hu) (H _ v (min_le_right ..))
  have hr: Poster v (regulatorF G P):= hZ.covered.tab
  have hx: Poster v (forceK G P (regulatorF G P) K.penalty B):=
    Poster.amounts (gift_lane B _ he hv) (hr.reverse.forge hr)
  let n : ℕ→Side := fun i => ⟨i+1, Nat.zero_lt_succ _⟩
  have hn : Tendsto (fun i => (n i).val) atTop atTop :=
    tendsto_atTop_mono (fun i=> show i ≤ i+1 by omega) tendsto_id
  let w : Armada n (fun i=>n i*P.L) P K:= ⟨fun _=>rfl⟩
  refine ⟨hx.skinny hη', h P hJ hP B _ _ _ _ _ w hn he hF hr ?_ (fun i=> Classical.arbitrary _) (fun i=> regulator_turn _ hP _)⟩
  rintro p hp
  rw [← hJ]; exact (hZ.base hp).mono (le_abs_self _)

lemma complete_ticket (S : StepData c f) (t : S.Choices) (h : S.patch.Branches S.kernel G)
    (B : Bed) (hB : B.metric.strip (inch S.patch.L * σ) Ω) (hσ : 0<σ) :
    let U := clothe G S; let F:=postroom (G:=G) S t (inch S.patch.L)
    Jaunt (approached (repackM U U (frontR G S B+F.transpose*F)))
      (forceK G S.patch (regulatorF G S.patch) S.kernel.penalty B) 0 := by
  classical
  intro U F
  let T := frontR G S B
  rw [show repackM U U (T+Fᵀ*F)=repackM U U T+repackM U U (Fᵀ*F) from rfl, prom_addition,
    repack_multiply _ (unitSplit G S 0),repack_rotate,prom_mul] -- adjust
  have he:= regulator_turn S h t
  exact (gift_turn B hσ hB).plus (he.takes.hoist he)

end YM.WilsonBulk
