import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Walks

set_option warningAsError false

/-!
# Pointwise dues on complete jet lists

Keep both weighted directions before inverse or row/column
summation. No Estimate on multilinear forms in a global Hilbert norm
is required in the budget hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix MeasureTheory Pressure
  Pressure.Tube Bid Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
  Next.SectorChange.Wisps Push.SectorMeasure FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent.Affine (Ceiling zero_null)
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {σ C P : ℝ}

lemma AtCap.dueJet {v : Directions G c → E} {B : Directions G c} (h : AtCap k C v B) (hC : 0≤C)
    (l : List (Atom G c)) (hl : l.length ≤ k) : ‖jet atom v l B‖ ≤ C := by
  refine (ContinuousMultilinearMap.le_of_opNorm_le (h.op l.length hl) (atom ∘ l.get)).trans ?_
  apply mul_le_of_le_one_right hC
  exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => atom_small (l.get i))).trans_eq (by simp)

structure Due (d : ℝ) (o z : Site c) (k : ℕ) (C : ℝ) (v : Directions G c → E) (B : Directions G c) : Prop where
  smooth : ContDiffAt ℝ k v B
  row (l : List (Atom G c)) (hl : l.length ≤ k) : (meterMark G c d).pay l o *
    ((FreeResolvent.native c).weight d o z * ‖jet atom v l B‖) ≤ C
  col (l : List (Atom G c)) (hl : l.length ≤ k) : (meterMark G c d).pay l z *
    ((FreeResolvent.native c).weight d z o * ‖jet atom v l B‖) ≤ C

namespace Due
variable {o z : Site c} {B : Directions G c} {v : Directions G c → E}
lemma congr_germ {w : Directions G c → E} (h : Due σ o z k C v B) (he : w =ᶠ[𝓝 B] v) :
    Due σ o z k C w B := by
  refine ⟨h.smooth.congr_of_eventuallyEq he,fun l hl => ?_,fun l hl => ?_⟩ <;> rw [identical _ he]
  · exact h.row l hl
  exact h.col l hl
lemma weaken (h : Due σ o z k C v B) (he : C≤P) : Due σ o z k P v B :=
  ⟨h.smooth,fun l hl => (h.row l hl).trans he,fun l hl => (h.col l hl).trans he⟩
lemma post (h : Due σ o z k C v B) (L : E →L[ℝ] H) :
    Due σ o z k (‖L‖*C) (fun B => L (v B)) B := by
  have hp (a b) (l : List (Atom G c)) (hl : l.length≤k)
      (ht : (meterMark G c σ).pay l a*((FreeResolvent.native c).weight σ a b*‖jet atom v l B‖) ≤ C) :
      (meterMark G c σ).pay l a*((FreeResolvent.native c).weight σ a b*‖jet atom (L∘v) l B‖) ≤ ‖L‖*C := by
    rw [show jet atom (L ∘ v) l B=_ from jet_linear _ _ _ (smooth_of_le h.smooth hl)]
    apply le_trans _ (mul_le_mul_of_nonneg_left ht (norm_nonneg L))
    rw [mul_left_comm ‖L‖,mul_left_comm ‖L‖]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (L.le_opNorm _) ((FreeResolvent.native c).weight_nn ..)) (pay_pos ..).le
  exact ⟨L.contDiff.contDiffAt.comp B h.smooth,fun l hl => hp _ _ l hl (h.row l hl),fun l hl => hp _ _ l hl (h.col l hl)⟩
lemma funded_zero (h : 0 ≤ C) : Due σ o z k C (0:Directions G c→E) B := by
  refine ⟨contDiffAt_const,fun i _ => ?_,fun i _ => ?_⟩ <;> rw [zero_null,norm_zero,mul_zero,mul_zero] <;> exact h
lemma scale (h : Due σ o z k C v B) (hp : 0≤C) (u : ℝ) : Due σ o z k (‖u‖*C) (fun x => u • v x) B := by
  let L := u • ContinuousLinearMap.id ℝ E
  have he : ‖L‖ ≤ ‖u‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by simp only [L,_root_.smul_apply,ContinuousLinearMap.id_apply,norm_smul]; rfl
  exact (h.post L).weaken (mul_le_mul_of_nonneg_right he hp)
end Due

/-- From genuine V reader locality. Works through every order *in* the
same working chart. For a longer path term, offer a radius for that path first.
Uses an unmasked assertion of smoothness ONLY of this function with settings
held fixed (`AtCap`). -/
lemma charge {o y : Site c} {V : Config G c} {r : ℕ}
    (v : Config G c → E) (B : Directions G c) (hp : Housed (E:=G.El) o r v)
    (he : ¬ separation o y ≤ r → ∀ U : Config G c, v U=0)
    (h : AtCap k C (fun b => v (increment V b)) B) (hc : 0≤C) {δ : ℝ} (hh : 0≤δ) :
    Due δ o y k (Real.exp ((1+2*k)*δ*r)*C) (fun b => v (increment V b)) B := by
  let F (b : Directions G c) := v (increment V b)
  have hv : Housed (E:=G.Color) o r F := by
    intro a b he; apply hp
    intro i hi; exact congr_arg (fun z => G.lieExp z * V i) (he i hi)
  have hX (l : List (Atom G c)) (hl : l.length≤k) : ‖jet atom F l B‖≠0 → separation o y≤r ∧
      ∀ i ∈ l, separation o (hearth i)≤r := by
    intro ht
    have hz : jet atom F l B≠0 := fun hy => ht (by rw [hy,norm_zero])
    refine ⟨?_,jet_home hv _ (smooth_of_le h.smooth hl) hz⟩
    by_contra hy; rw [show F=0 from funext fun v => he hy _, zero_null] at hz; contradiction
  refine ⟨h.smooth,fun l hl => ?_,fun l hl => ?_⟩
  · exact (local_fare (o:=o) (y:=y) l (h.dueJet hc l hl) (norm_nonneg _) hh hl (hX l hl)).1
  exact (local_fare (o:=o) (y:=y) l (h.dueJet hc l hl) (norm_nonneg _) hh hl (hX l hl)).2

lemma normEventually {B : Directions G c} (he : ‖B‖ < 1) : ∀ᶠ b in 𝓝 B, ‖b‖ ≤ 1 := by
  filter_upwards [((continuous_norm (E:=Directions G c)).tendsto B).eventually (gt_mem_nhds he)] with b hb
  exact hb.le

lemma grayPrice (S : StepData c f) (s : Signed) (V : Config G c) (j : Atom G f) (p : Cell f) (B : Directions G c) (k : ℕ)
    (he : ‖B‖ < 1) {δ : ℝ} (hd : 0 ≤ δ) :
    let C := Real.exp ((1+2*k)*δ*(5:ℕ)) * bladeMoney G (k+1)
    Due δ (s.act (S.ratio.parent p.1)) (S.ratio.parent j.1.1) k C (gray S s p V j) B := by
  intro C
  let F (U : Config G c) := plaquetteJet S U s p (atom j)
  have h : gray S s p V j =ᶠ[𝓝 B] fun b => F (increment V b) := (normEventually he).mono fun _ h => gray_agrees S s p V j h
  have hv : AtCap k (bladeMoney G (k+1)) _ B := AtCap.fromCeiling (gray_cap (k:=k) S s p V j)
  have ht := charge (r:=5) F B (face_houses S s p (atom j)) (y:=S.ratio.parent j.1.1) (fun h v => face_needs S s p v j h) (hv.germ h.symm) (blade_nn ..) hd
  exact ht.congr_germ h

def flight (G : Gauge) (σ δ : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((1+2*k)*δ*(5:ℕ))*lineMoney G k (σ/2)
lemma flight_nn (G : Gauge) (σ δ : ℝ) (k : ℕ) : 0≤flight G σ δ k := mul_nonneg (Real.exp_pos _).le (lineMoney_nn ..)

lemma linePrice (S : StepData c f) (s : Signed) (V : Config G c) (j : Atom G f) (x : Site f) (m : Slot)
    (B : Directions G c) (k : ℕ) (he : ‖B‖ < 1) {σ δ : ℝ} (hσ : 0<σ) (hd : 0≤δ) (h : (1+2*k)*δ ≤ σ/2) :
    Due δ (s.act (S.ratio.parent x)) (S.ratio.parent j.1.1) k
      (Real.exp (σ*m.length)*flight G σ δ k) (line S s V j x m) B := by
  let F := strand S s (atom j) x m
  have hr : line S s V j x m =ᶠ[𝓝 B] fun b => F (increment V b) := (normEventually he).mono fun _ hi => line_agrees S s V j x m hi
  let C := lineMoney G k (σ/2)
  have hc := lineMoney_nn G k (σ/2)
  have hv : AtCap k (C * Real.exp (σ/2*m.length)) _ B := AtCap.fromCeiling (line_cap S s V j x m k (half_pos hσ))
  have ht := charge F B (strand_houses S s x m (atom j)) (y:=S.ratio.parent j.1.1) (fun h v => strand_needs S s v j x m h) (hv.germ hr.symm)
    (mul_nonneg hc (Real.exp_pos _).le) hd
  apply (ht.congr_germ hr).weaken
  unfold flight
  calc
    _ = Real.exp ((1+2*k)*δ*↑(m.length+5)+σ/2*m.length) * C := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (σ*m.length+(1+2*k)*δ*↑(5:ℕ)) * C := by
      apply mul_le_mul_of_nonneg_right _ hc; apply Real.exp_monotone; push_cast; nlinarith only
        [mul_le_mul_of_nonneg_right h (show 0 ≤ (m.length:ℝ) by positivity)]
    _ = _ := by rw [Real.exp_add,mul_assoc]
end YM.AnalyticBridge.Covariance
