import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.NoHole

/-!
# Ordered left-Lie no-hole inverse budgets (actual estimates at the flat configuration)

Identity-completed precision on non-tree + tree slots. One family across
periodic volume, trees, compression/column windows, shift u and paths of
bounded true-length cost (see Sheet). Same charges incl integrable drains in
tag and positive-order tests. No random commissioning or coupling input. Use
`.total`/`.fields` on these books to perform extra expenditures (Receipts).
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.NoHole
open Lattice Wilson RG Function Filter WardBin.Lies Exterior FreeResolvent Affine Mark TestD Lever Window Tree Precision
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {ι : Type*} [Fintype ι]

/-- max k true Lie derivatives with complete Taylor slot weights, also of
the literal one-tag difference. δ is the decreased Taylor mark width, d the
extra tag width, γ the matrix rate. No extra (card period) price in either
step. Does not exclude equality, coincidence or null compression cases. -/
structure Paid (S : StepData c f) (a : ι → Site c) (k : ℕ) (δ d γ : ℝ) (M N : ℕ → ℝ)
    (F : Forest S.ratio → Config G c → Matrix ι ι ℝ) (field : Config G c := 1) : Prop where
  base (T : Forest S.ratio) : Book (native c) a a Prod.fst k δ γ M (F T) field
  variation (T U : Forest S.ratio) (v : Site c) : changed S T U v →
    ChangedBook (native c) a a Prod.fst k δ d γ v N (F U-F T) field

section produce
variable (p : Clip) (t : S.Choices) {W : PathData G} {u σ M : ℝ}
variable (hs : 0 < σ) (hm : 0 ≤ M) (hW : Sheet W σ M) (he : Bid.Larger (G:=G) S) (hu : 0 ≤ u)
include hs hm hW he hu
variable {n k : ℕ}


variable [DecidableEq ι]

private lemma tag_in_pane (r : Admit) {T U : Forest S.ratio} {v : Site c} (ht : changed S T U v) {e : ι → raw G f} (hi : Injective e)
    (l : List (raw G c)) (hl : l.length < n) :
    let d := width G S.patch S.kernel p n M σ
    let b := home (r:=1) S ∘ e
    let F := fun T y => ((paddedGram S t p W r T) y).submatrix e e
    Here (ray G c) (native c) b Prod.fst d (4*(n+1:ℕ)*d) v l (earnings G S.patch S.kernel p n M σ * drain u * drain u)
      (over (resolver (F T) u) 1) (over (resolver (F U) u) 1) := by
  intro d b F; let H := TestD.action (limitTo (crest S (p:=p) (W:=W) (T:=T) (U:=U) t r) e) u
  have hP := gauged G S.patch S.kernel p n hs hm
  have hp (x) (hx : x ∈ Set.Icc (0:ℝ) 1) := shrink (mast (p:=p) (n:=n) S t hs hm hW he ht r hx) hi
  have h (x) (hx : x ∈ Set.Icc (0:ℝ) 1) := (hp x hx).cost (none::l.map some) (by simp [hl]) hP hu
    (position_move _ _ hP.pos.le) ((home_volume _ _ _ hP.pos).comp hi)
  simp only [charges,List.length_cons,Nat.add_one_ne_zero,↓reduceIte,mul_one] at h
  have hT y : H (y,0) = over (resolver (F T) u) 1 y := by unfold H TestD.action limitTo; rw [now]; rfl
  have hU y : H (y,1) = over (resolver (F U) u) 1 y := by unfold H TestD.action limitTo; rw [thenAt]; rfl
  constructor; intro i j
  have h0 (x) (hx : x ∈ Set.Icc (0:ℝ) 1) : ContDiffAt ℝ (↑(l.length+1):ℕ∞ω) H (0,x) := smooth_of_le ((hp x hx).sees hu hP.r0) hl
  have hr := recovers l h0 h i j; rw [funext hT, funext hU] at hr; exact hr

/-- All principal windows, or the whole padded inverse. Tree change in
that same set, with its own spatial gain AND no loss of shift integrability.
Choose n=k+1 for a joint receipt (extra order for tag interpolation). -/
theorem principalPaid (hk : k < n) (r : Admit) {e : ι → raw G f} (hi : Injective e) :
    let d := width G S.patch S.kernel p n M σ; let E := earnings G S.patch S.kernel p n M σ
    Paid S (home S ∘ e) k (narrow n d) d (4*(n+1:ℕ)*d)
      (fun j => surcharge G j * charges j 1 E (drain u)) (fun j => surcharge G j * (E * drain u * drain u))
      (fun T => resolver (fun V => (paddedGram S t p W r T V).submatrix e e) u) := by
  intro d E
  have hp := gauged G S.patch S.kernel p n hs hm
  have h T := principal (padded_data t p T r n hs hm hW he) hp (home_volume _ _ _ hp.pos) hu hi
  refine ⟨fun T => (h T).mono le_rfl le_rfl hk.le (fun _ _ => le_rfl),fun T U v hTU => ?_⟩
  apply leaseChange (M:=fun _ => E*drain u*drain u) (smooth_over.mpr ((h T).smooth.prod hk.le)) (smooth_over.mpr ((h U).smooth.prod hk.le))
    (narrow_nn n hp.pos.le) (narrow_use hp.pos.le hk.le) (fun _ _ => mul_nonneg (mul_nonneg hp.meter_abs (drain_pos hu).le) (drain_pos hu).le)
    (fun j hj b w => tag_in_pane p t hs hm hW he hu r hTU hi (List.ofFn w) (List.length_ofFn.trans_lt ((b.length_le.trans hj).trans_lt hk)))



variable {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]








end produce
end YM.SelectedOrderedKernels.NoHole
