import YM.RG08.Gaussian.PeriodicInverse

/-! # Joint flat frame completion prior to projection
Use the already available pre-block tilt `Stationary.post_cert`. No step
caller will need to know or change ANY real PathData or period thresholds
in order to issue the estimate. The Bed certificate here is auxiliary; the
unmodified quadratic on the canonical formal history agrees exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice RG Exterior Bloch Precision Matrix Laurent Work.F08
open Stationary Next.Free
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side}

abbrev quietCompletion (G : Gauge) (P : Patch) : Eye (Fin 0) (Acts G P) := 0

theorem g_light (P : Patch) (σ : ℝ) (h : σ≤1) :
    Spotlight P (quietCompletion G P) σ (Real.exp 4) :=
  ⟨h,⟨fun _ _ => rfl,fun _ _ => differentiableAt_const _⟩,le_rfl,fun i => i.elim0⟩

theorem g_pass (S : StepData c f) (hp : S.patch.Branches S.kernel G) (t : S.Choices) :
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S t (inch S.patch.L))))
      (CanonR (quietCompletion G S.patch) false).tab 0 := by
  let Z : Corn (Co c (Fin 0)) →L[ℝ] Bang G c f := 0
  have h : Turns (quietCompletion G S.patch) (billZ S Z) := by
    refine ⟨0,fun u => ?_,fun i q _ v => ?_⟩
    · simp [Z,billZ]
    ext1 j; simp [tune,quietCompletion]
  have hx := (regulator_tour S t false Z h hp (fun _ => rfl)).tab
  dsimp only [cardM] at hx
  rw [zero_hat S hp] at hx; exact hx

def quadraticJoint (G : Gauge) (S : StepData c f) (M : Matrix (Body 1 f) (Body 1 f) ℝ) :=
    (butt G c f)ᵀ * patron G M * butt G c f +
      S.kernel.penalty • ((fortune G S)ᵀ * fortune G S)

def wideH (G : Gauge) (S : StepData c f) (t : S.Choices)
    (M : Matrix (Body 1 f) (Body 1 f) ℝ) :=
    quadraticJoint G S M + (postroom (G:=G) S t (inch S.patch.L))ᵀ * (postroom S t (inch S.patch.L))

lemma g_bed (S : StepData c f) (hp : S.patch.Branches S.kernel G) (t : S.Choices) (B : Bed)
    {w C : ℝ} (he : 0<w) (hv : B.metric.strip (inch S.patch.L*w) C) :
    Jaunt (approached (repackM (clothe G S) (clothe G S)
        (wideH G S t (K (B.metric.acts f)))))
      (forceK G S.patch (CanonR (quietCompletion G S.patch) false).tab S.kernel.penalty B) 0 := by
  let T := postroom S t (inch S.patch.L) (G:=G)
  let Y := clothe G S
  have hx := gift_turn (S:=S) (G:=G) B he hv
  have hf := g_pass S hp t
  have hr : Jaunt (approached (repackM Y Y ((T)ᵀ*T)))
      (fun p => ((CanonR (quietCompletion G S.patch) false).tab (-p))ᵀ *
         (CanonR (quietCompletion G S.patch) false).tab p) 0 := by
    rw [repack_multiply _ (unitSplit G S 0),repack_rotate,prom_mul]
    exact hf.takes.hoist hf
  rw [wideH,show repackM _ _ (_ + _) = repackM Y Y (frontR G S B)+repackM Y Y (Tᵀ*T) from rfl,prom_addition]
  exact hx.plus hr

/-- Terms use `giftQ`/`frontR` unscaled. `j` chosen before P (including L).
The pre-strip is uniform even on P and u, including tags. -/
theorem joint_universal (G : Gauge) (k : KernelChoices) (j : ℕ) (hj : 4 ≤ j) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ P : Patch, P.J=j → P.Branches k G →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Train P.J,
        ∃ R : Row (ParcelG G P.L) (ParcelG G P.L), R.strip σ M ∧
          ∀ (c f : Side) (h : f.val=c.val*P.L.val),
            let S : StepData c f := ⟨P,k,h⟩
            ∀ t : S.Choices, repackM (clothe G S) (clothe G S)
                (wideH G S t ((hessian (pink k.penalty u)).acts f)) * R.acts c=1 := by
  obtain ⟨v,r,ε,D,hv,hr,hε,hD,H⟩ := bid_bed k.penalty 0 k.penalty_pos le_rfl hj
  obtain ⟨δ,A,hδ,hδ',hA,Ha⟩ := amasses G
  let w := min r δ
  have hw : 0<w := lt_min hr hδ
  have hl : w ≤ 1 := (min_le_right ..).trans (hδ'.trans (by norm_num))
  let B := tribute2 G j (Real.exp 4) A
  obtain ⟨η,C,hη,hp,hC,Hc⟩ := post_cert G j k ε w D |B| hε hw hl hD.le (abs_nonneg _)
  refine ⟨η/4,by positivity,fun P ha hK => ?_⟩
  obtain ⟨M,hM,T⟩ := freezer_row (slabW G P.L) (booth_continuous ..) hη hC
  refine ⟨M,hM,fun u => ?_⟩
  let Z := CanonR (quietCompletion G P) false
  subst j
  let p : Clip := ⟨v,v/32,1,hv,by positivity, by linarith,zero_lt_one⟩
  obtain ⟨b,h₁,h₂,h₃,-,-⟩ := H p le_rfl u
  have ht := conquer hK hw (g_light P _ hl) (Ha P.L w (min_le_right ..))
  have hP : Poster w Z.tab := ht.covered.tab
  have hh : B ≤ |B| := le_abs_self _
  have hr : b.metric.strip (inch P.L*w) D := strip_mono h₂.2.1
    ((mul_le_of_le_one_left hw.le (inch_le _)).trans (min_le_left ..)) le_rfl
  let m (i : ℕ) : Side := ⟨i+1,Nat.succ_pos _⟩
  let n (i : ℕ) := m i*P.L
  let W : Armada m n P k := ⟨fun _ => rfl⟩
  let t (i) : (W.boot i).Choices := (fun _ => (P.center, 1), fun _ => P.center)
  let F := forceK G P Z.tab k.penalty b
  have hm : Tendsto (fun i => (m i).val) atTop atTop :=
    tendsto_atTop_mono (fun i => show i ≤ i+1 by omega) tendsto_id
  have hF : Poster η F :=
    Poster.skinny (Poster.amounts (gift_lane b _ hr hw) (hP.reverse.forge hP)) hp
  have hX : Freezer (slabW G P.L|>.dual) (slabW G P.L) F η C :=
    Hc P rfl hK b p D Z.tab m n W hm hr h₃ hP (fun p hz => (ht.base hz).mono hh) t
      (fun i => g_pass (W.boot i) hK (t i))
  obtain ⟨R,hR,hY⟩ := T F hF hX (fun p hS => judge hm
      (fun i => g_bed (W.boot i) hK (t i) b hw hr) hF hη hS)
  refine ⟨R,hR,?_⟩
  intro c f h S t
  have hc : (hessian (pink k.penalty u)).acts f=K (b.metric.acts f) := by
    rw [← h₁.diag,hessian_acts (show Whole b.diagonal from ⟨_,_,(mul_pos (inch_pos _) hw),
      strip_mono h₂.1 ((mul_le_of_le_one_left hw.le (inch_le P.L)).trans (min_le_left ..)) le_rfl⟩),K,K,
      Matrix.mul_assoc,Matrix.mul_assoc, (h₃ f).same]
  rw [hc]
  convert! hY c _ (g_bed S hK t b hw hr)

end YM.RG08
