import YM.AnalyticNext.QUARTIC_MATCH.Local.Centerline
import YM.AnalyticNext.QUARTIC_MATCH.Local.Input
import YM.AnalyticNext.QUARTIC_MATCH.Local.Limits

/-!
# Budget of directions at center and beyond

Only needs the given tower and purchases. Use at the *same* parameters for
acceleration. External labels include direction anchors even antipodal and
repeated links. Constants not seeding R4 from a weakened norm embedding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain Premium Evoke Budget
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Wages
variable (G : Gauge)
open Green (wt)
lemma pure_path (k m j : ℕ) (hm : k ≤ m) (hk : k ≤ 4) (u D κ η C : ℝ) (hp : 0<u) (he : boom u ≤ η) (hκ : 0<κ) :
    ∃ R : ℝ,0 ≤ R ∧ ∀ (c f : Side) (S : StepData c f) (p : Clip) (W : PathData G) (a : S.Choices) (σ τ K Λ R3 R4 : ℝ),
      S.patch.J=j → S.kernel.penalty=κ → S.patch.Branches S.kernel G → W.Bounds p τ K Λ → Rotate.Led W S.patch.L m (boom u) σ D R3 R4 →
        ∀ U : Cross S.ratio.count (TypeFace 1) (TypeFace 1),Evoke.motion S U η C →
        ∀ (x : Fin k→Cell (Per c)) (z : Fin k→G.Color) (i : Fin k),
        span (rate u) (x i).1 (fun k => (x k).1)* |iteratedFDeriv ℝ k (cash S a p W) 0 (fun k => external (installed S.ratio U) (x k) (z k))| ≤
          R*assistance S.patch.L R3 R4*∏ i, ‖z i‖ := by
  obtain ⟨R,hR,H⟩ := awards G j m (boom u) u D κ (booms hp) hp hκ
  have hv := zero_le_one.trans (costS η C)
  refine ⟨R*smoothC η C^k,mul_nonneg hR (pow_nonneg hv _),?_⟩
  intro c f S p W a σ τ K Λ R3 R4 hj hv' hB hW hl A hA x z i
  let l := S.ratio.count
  let V := cash S a p W
  let b (k) := external (installed S.ratio A) (x k) (z k)
  let Z (i) := S.ratio.embed (x i).1; let X i := (x i).1
  let d (k) := smoothC η C*‖z k‖
  have hd (k) : 0≤d k := mul_nonneg hv (norm_nonneg _)
  let P := Wages.account l none Z (fun _ => boom u) d hd
  let m' := span (rate u) (X i) X
  have he' := travels none Z (fun _ => boom u) d hd l (η:=boom u) fun _ => (abs_of_pos (booms hp)).le
  have hQ : Stamp P Finset.univ S.patch.L u m' (Z i) := by
    have h := journey hp P i Z l hk (fun _ _ => rfl)
    rw [show span (rate u/l.val) (Z i) Z=m' from span_coarse S _ _ _] at h; exact h
  have hG : ∀ i,Presents S P i (b i) := fun i => offers S (booms hp) he A hA P (x i) (z i) i (by simp [P,Wages.account]) rfl (fun _ => rfl)
  have hx := H _ _ S p W a σ _ _ _ _ _ hj hv' hB hW hl _ P Finset.univ b (by simpa using hm) rfl he' hG (X i) m' (span_pos ..).le hQ
  have hV : ContDiffAt ℝ ω V 0 := by
    -- directly via charged
    rw [show V=(fun z => mainTerm p W (represent z.2.1)+S.kernel.penalty*∑ y : Site c,∑ i, coins S a y i z) from funext (Budget.charged S a p W)]
    apply ContDiffAt.add
    · let f := fun x : Dir G f => mainTerm p W (represent x); have hf : ContDiffAt ℝ ω f 0 := Work.F02.mainTerm_contDiffAt hW (A:=represent) (fun i => (represent_smooth ..).contDiffAt)
      exact hf.comp (f:=fun z : JointSpace G c _ => z.2.1) (0:JointSpace G c _) (by fun_prop)
    exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => coin_smooth S a hB i j)
  rw [univEstimate b _ _ hV] at hx
  exact hx.trans_eq (by unfold target P Wages.account d; simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,Fintype.card_fin]; ring)

section movement
open Tracks
variable {u D κ η C : ℝ}

/-- Charge the rough leg also when sending from another family of external
positions. Apply twice, with particular M to bill a spanning tree. -/
theorem bending (j m : ℕ) (hm : 3 ≤ m) (hp : 0 < u) (he : boom u ≤ η) (hκ : 0<κ) : ∀ D : ℝ,∃ R : ℝ,0 ≤ R ∧
    ∀ (c f : Side) (S : StepData c f) (p : Clip) (W : PathData G) (a : S.Choices) (σ τ K Λ R3 R4 : ℝ),
      S.patch.J=j → S.kernel.penalty=κ → S.patch.Branches S.kernel G → W.Bounds p τ K Λ → Rotate.Led W S.patch.L m (boom u) σ D R3 R4 →
        ∀ U : Cross S.ratio.count (TypeFace 1) (TypeFace 1),Evoke.motion S U η C → ∀ (x y : Cell (Per c)) (v w : G.Color),
          let r := leg (cash S a p W) 0 (external (installed S.ratio U) x v) (external (installed S.ratio U) y w)
          ∀ (b b' : Site c) (t M : ℝ) (z : Vertical G c f), let e := S.ratio; |t|≤ boom u → 0 ≤ M →
            (∀ i, M*wt (u/e.count.val) i (e.embed b') ≤ wt (boom u/e.count.val) i (e.embed x.1)*wt (boom u/e.count.val) i (e.embed y.1) *
              wt (-t/e.count.val) i (e.embed b)) →
            M* |r (polar S t (e.embed b) z)| ≤ R*assistance S.patch.L R3 R4*‖v‖*‖w‖ * shares S z := by
  intro D; obtain ⟨R,hR,H⟩ := awards G j m (boom u) u D κ (booms hp) hp hκ
  let K := roughC (boom u)
  let Q := smoothC η C; have hQ : 0 ≤ Q := zero_le_one.trans (costS ..); have hK : 0≤K := zero_le_one.trans (rough_ge _)
  refine ⟨R*Q*Q*K,by positivity,?_⟩
  intro c f S p W a σ τ K' Λ R3 R4 hs hk hB hP hL U hU x y v w r b b' t M z e ht hy hx
  let Z := ((0:Dir G c), polar S t (e.embed b) z)
  let F := cash S a p W
  let A i j := external (installed S.ratio U) i j (G:=G)
  let T := ![A x v,A y w,Z]
  let q := shares S z
  let c := ![e.embed x.1,e.embed y.1,e.embed b]
  let f₁ := ![boom u,boom u,-t]
  let d := ![Q*‖v‖,Q*‖w‖,K*q]
  have hd i : 0 ≤ d i := by
    fin_cases i
    · exact mul_nonneg hQ (norm_nonneg _)
    · exact mul_nonneg hQ (norm_nonneg _)
    · exact mul_nonneg hK (shares_nonneg ..)
  let P := Wages.account S.ratio.count (some (2:Fin 3)) c f₁ d hd
  have hg : ∀ i,Presents S P i (T i) := by
    intro i; fin_cases i
    · exact offers S (booms hp) he U hU P x v 0 (by intro H; exact (by decide : (some (2:Fin 3))≠some 0) H) rfl (fun _ => rfl)
    · exact offers S (booms hp) he U hU P y w 1 (by intro H; exact (by decide : (some (2:Fin 3))≠some 1) H) rfl (fun _ => rfl)
    exact contributes S (booms hp) ht P z (e.embed b) 2 rfl rfl rfl (fun _ => rfl)
  have hχ : tollRate P S.patch.L (boom u) := by
    apply (show tollRate P S.ratio.count (boom u) from travels _ _ f₁ d hd S.ratio.count fun i => ?_)
    fin_cases i
    · exact (abs_of_pos (booms hp)).le
    · exact (abs_of_pos (booms hp)).le
    exact (abs_neg t).trans_le ht
  have hv : Stamp P Finset.univ S.patch.L u M (S.ratio.embed b') := by
    intro i; simp only [price,Fin.prod_univ_succ];
    convert! hx i using 1; dsimp [P,Wages.account,d,e,c,f₁]; ring
  have h := H _ _ S p W a σ _ _ _ _ _ hs hk hB hP hL _ P Finset.univ T (by simpa using hm) rfl hχ hg b' M hy hv
  have hF : ContDiffAt ℝ ω F 0 := by
    rw [show F=(fun z => mainTerm p W (represent z.2.1)+S.kernel.penalty*∑ y,∑ i, coins S a y i z) from funext (Budget.charged S a p W)]
    apply ContDiffAt.add
    · have hf : ContDiffAt ℝ ω (fun x : Dir G f => mainTerm p W (represent x)) 0 := Work.F02.mainTerm_contDiffAt hP (A:=represent) (fun i => (represent_smooth ..).contDiffAt)
      exact hf.comp (f:=fun z : JointSpace G _ f => z.2.1) (0:JointSpace G _ f) (by fun_prop)
    exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => coin_smooth S a hB i j)
  have HH : bill Finset.univ T F 0=r Z.2 := (univEstimate T F _ hF).trans (D3_jet F 0 (A x v) (A y w) Z)
  change M* |r Z.2| ≤ R*Q*Q*K*_ * ‖v‖*‖w‖ * q; rw [← HH]; exact h.trans_eq (by
    change _*(∏ i,d i)=_; simp only [Fin.prod_univ_succ,d]; dsimp; ring)
end movement
end Wages
end YM.AnalyticNext.QuarticMatch.Local
