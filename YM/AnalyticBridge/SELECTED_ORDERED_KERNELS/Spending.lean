import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Prospects

/-!
# Turning certified segment data into ordered expenditures at BOTH ends

The physical kernel `fun T => Φ ∘ finished H x A T k` is evaluated on
true Config. Includes ordered Taylor-slot, NearStar, full growing direction
and one-site tag terms simultaneously, through any fixed finite order. Uses
regularity all along the single-tag segment as the input to the general
`Small.aux_pass` also when *centred* at the real V. In particular no freezing
the frames in the passage from `jet` to `leftDerivs`. Segment is a proof
parameter, not a continuation on which physical positivity is presumed from
endpoints alone. Floors just proved supply that for our actual uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Next.SectorChange Set
  YM.Pressure FreeResolvent Affine TestD Window Mark Matrix NoHole Lever
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {H : Tube G S} {r s M V' d γ N x u ρ : ℝ}
  {q n j : ℕ} {A : Stores S} {k : S.Choices} {V : Config G c}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → raw G f} {m : ℕ → ℝ}

abbrev Full (G : Gauge) (f : Side) := Matrix (raw G f) (raw G f) ℝ

def Spend (H : Tube G S) (x : ℝ) (A : Stores S) (k : S.Choices) (V : Config G c) (e : ι → raw G f)
    (q n : ℕ) (d : ℝ) (m : ℕ → ℝ) (N : ℝ) (R : Full G f → Matrix ι ι ℝ) := let γ := Small.togetherAt n d
  NoHole.Receipt S (home S ∘ e) q γ (coins G S.patch γ) (fun j => offFee G j*m j) (fun j => offFee G j*N) (fun T => R ∘ finished H x A T k) V

abbrev Design (H : Tube G S) (x : ℝ) (A : Stores S) (k : S.Choices) (V : Config G c) (e : ι → raw G f)
    (q n : ℕ) (d N : ℝ) (R : Full G f → Matrix ι ι ℝ) := Spend H x A k V e q n d (fun _ => N) N R

omit [DecidableEq ι] in
lemma segment_spend (R : Full G f → Matrix ι ι ℝ) (he : Injective e) (hd : 0 < d) (hq : q<n) (hg : d ≤ γ) (hN : 0 ≤ N)
    (hm : ∀ j ≤ q, 0 ≤ m j) (hp : ∀ j ≤ q, ∀ p : OrderedFinpartition j, m p.length ≤ m j ∧ m (p.length+1) ≤ N)
    (h : ∀ T U v, changed S T U v → ∀ t ∈ Icc (0:ℝ) 1, let F := R ∘ line H x A k V T U; ContDiffAt ℝ n F (0,t) ∧ ∀ l : List (Option (raw G c)),
      l.length ≤ n → Bill (park (native c) hearth d v) (native c) (home S ∘ e) (home S ∘ e) l γ (m l.length) (jet (guides (ray G c)) F l (0,t))) :
    Spend H x A k V e q n d m N R := by
  have hZ (T U v) (hv : changed S T U v) : Small.Aux (home S ∘ e) n d γ m 0 V (R ∘ finished H x A T k) (R ∘ finished H x A U k) v := by
    refine ⟨R ∘ line H x A k V T U, fun y => ?_, fun y => ?_, h T U v hv⟩
    · simp only [Small.around,add_zero,Function.comp_apply,line_left]; rfl
    simp only [Small.around,add_zero,Function.comp_apply,line_right]; rfl
  have hh : Paid S (home S ∘ e) q (narrow n d) d γ (fun j => offFee G j*m j) (fun j => offFee G j*N) (fun T => R ∘ finished H x A T k) V := by
    rw [← Motion.increment_zero V]; nth_rw 1 [← map_zero (paint G c)]
    exact Small.aux_pass hZ hd.le hq (fun i => by rw [map_zero,Pi.zero_apply,norm_zero]; exact radius_pos ..) hN hm hp
  exact Small.boughtHere he hq.le hd hh hg

omit [DecidableEq ι] in
lemma design_spend (R : Full G f → Matrix ι ι ℝ) (he : Injective e) (hd : 0 < d) (hq : q<n) (hg : d ≤ γ) (hN : 0 ≤ N)
    (h : ∀ T U v, changed S T U v → ∀ t ∈ Icc (0:ℝ) 1, Bundle (guides (ray G c)) (park (native c) hearth d v) (native c) (home S ∘ e) (home S ∘ e)
      (R ∘ line H x A k V T U) (0,t) n γ N) : Design H x A k V e q n d N R :=
  segment_spend _ he hd hq hg hN (fun _ _ => hN) (fun _ _ _ => ⟨le_rfl,le_rfl⟩) fun T U v hv t ht => ⟨(h T U v hv t ht).smooth,(h T U v hv t ht).bound⟩




structure Engine (H : Tube G S) (x : ℝ) (A : Stores S) (k : S.Choices) (V : Config G c) (n : ℕ) (s M r d V' : ℝ) (Φ : Full G f → Full G f) : Prop where
  price : Price s M r d 1 V' 1 n
  volume : (native c).Volume (home S (G:=G) (r:=1)) d V'
  budget (T U : Forest S.ratio) (v : Site c) : changed S T U v → ∀ t ∈ Icc (0:ℝ) 1,
    Knew (park (native c) hearth d v) (native c) (home S) (guides (ray G c)) (0,t) n s M r 1 (Φ ∘ line H x A k V T U)

namespace Engine
variable {Φ : Full G f → Full G f} (h : Engine H x A k V n s M r d V' Φ) (hu : 0 ≤ u) (hq : q<n)
include h hq


include hu


variable {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]




end Engine

structure Register (H : Tube G S) (x : ℝ) (A : Stores S) (k : S.Choices) (V : Config G c) (q n : ℕ) (M r d V' : ℝ) (Φ : Full G f → Full G f) : Prop where
  source : Design H x A k V id q n d M Φ
  inverse (u : ℝ) : 0 ≤ u → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → raw G f}, Injective e →
    Spend H x A k V e q n d (fun j => Sector.cost n M V' r u j) (Sector.count n M V' r*drain u*drain u) (fun F => resolve ((Φ F).submatrix e e) u)
  windows (u : ℝ) : 0 ≤ u → ∀ {I : raw G f → Type} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)] (Z : Survey I),
    Spend H x A k V id q n d (fun j => V'*Sector.cost n M V' r u j) (V'*(Sector.count n M V' r*drain u*drain u)) (fun F => Z.inspect (Φ F) u) ∧
      ∀ ρ, Z.Near (native c) (home S) ρ → Design H x A k V id q n d (patchFee d ρ M 1 V' (Sector.count n M V' r*drain u) n)
        (fun F => Z.inspect (Φ F) u - resolve (Φ F) u)


end YM.SelectedOrderedKernels.Selected
