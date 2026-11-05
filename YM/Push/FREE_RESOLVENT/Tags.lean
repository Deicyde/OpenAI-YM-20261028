import YM.Push.FREE_RESOLVENT.AffineGap
import YM.Push.FREE_RESOLVENT.Extant

/-!
# Local response to geometrical tree tag changes

Completed matrices, keep *all* inputs of W. The
no-hole resolution and cut mats share the same tree. For tag derivative
*sensitivities*, use the finite difference at fixed v (use locality test
of shape, not of truncated response). Tag not an empirical variable to use
in another kernel. The sizes include both the tagged and path-tail shifts,
no factoring 1/volume out from the tag response.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG.Patch Bloch Wilson RG Precision Exterior Matrix Lever Filter Function Set Shell Mark TestD Tree
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T U : Forest S.ratio} {p : Clip} {t σ A : ℝ}

def freeTo (G : Gauge) (S : StepData c f) (T : Forest S.ratio) : Active G T ↪ raw G f := ⟨plant T,plant_inj T⟩

def whole (S : StepData c f) (T : Forest S.ratio) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit) :=
    Shell.pad (freeTo G S T) ∘ block S k p W r

def changed (S : StepData c f) (T U : Forest S.ratio) (o : Site c) : Prop := ∀ i : Edge (Site f),
    S.ratio.parent i.1≠o → (i ∈ T.trunks ↔ i ∈ U.trunks)

lemma locate (T : Forest S.ratio) (e : Edge (Site f)) (i : G.ColorIndex) :
    (e.1,coord e.2,i) ∈ Set.range (freeTo G S T) ↔ e ∉ T.trunks := by
  constructor
  · rintro ⟨a,ha⟩
    have he : e=a.1.val := Eq.symm (Prod.ext (congr_arg (fun x : raw G f => x.1) ha) ((coord_iff ..).mp (congr_arg (fun x : raw G f => x.2.1) ha)))
    exact he.symm ▸ a.1.property
  intro h; exact ⟨(⟨e,h⟩,i),rfl⟩

lemma suits (G : Gauge) (o : Site c) (h : changed S T U o) : Shell.Stable o (home S) (freeTo G S U) (freeTo G S T) := by
  rintro ⟨x,i,j⟩ hx
  obtain ⟨w,rfl⟩ := axisEquiv.surjective i
  erw [locate U (x,w), locate T (x,w),h (x,w) hx]

section variation
variable (G) (P : Patch) (K : KernelChoices)

def gum (p : Clip) := min (headGap G P K p) 1
lemma gum_pos (p : Clip) : 0 < gum G P K p := lt_min (headGap_pos ..) zero_lt_one

def nuts (p : Clip) (k : ℕ) (A σ : ℝ) := 3*(stageCost G P K p k A σ+1)
lemma nuts_nn (p : Clip) (k : ℕ) (hs : 0 < σ) (ha : 0 ≤ A) : 0 ≤ nuts G P K p k A σ :=
  mul_nonneg (by norm_num) (add_nonneg (stage_nn _ _ _ _ hs ha) zero_le_one)

def width (p : Clip) (k : ℕ) (A σ : ℝ) := room (tier σ k/2) (nuts G P K p k A σ) (gum G P K p) k

def locker (p : Clip) (k : ℕ) (A σ : ℝ) := torusPay (Co P.L (PAC G 1)) (width G P K p k A σ)

lemma gauged (p : Clip) (k : ℕ) (hs : 0 < σ) (ha : 0 ≤ A) :
    Price (tier σ k/2) (nuts G P K p k A σ) (gum G P K p) (width G P K p k A σ) 1 (locker G P K p k A σ) 1 k := by
  have hg := half_pos (ordering hs k).1
  have hh := nuts_nn G P K p k hs ha
  have hx := gum_pos G P K p
  have hd : 0 < width G P K p k A σ := (room_grid hg hh hx k).1
  exact ⟨hx,hh,hg,rfl,le_rfl,torusPay_nn _ _ hd,zero_le_one,le_rfl⟩
end variation

section train
variable (S)
variable (k : S.Choices) {T U : Forest S.ratio} {p : Clip} {n : ℕ}
variable (hs : 0 < σ) (ha : 0 ≤ A) {W : PathData G} (hW : Sheet W σ A) (hb : Bid.Larger (G:=G) S)
variable {v : Site c} (ht : changed S T U v)



def crest (R : Admit) := mixture (whole S T k p W R) (whole S U k p W R)

include hs ha hW hb ht
lemma mast (r : Admit) {x : ℝ} (he : x ∈ Icc (0:ℝ) 1) :
    let α := tier σ n / 2; let d := width G S.patch S.kernel p n A σ
    Knew (Lever.park (native c) hearth d v) (native c) (home S) (guides (ray G c)) (0,x) n
      α (nuts G S.patch S.kernel p n A σ) (gum G S.patch S.kernel p) 1 (crest S k (T:=T) (U:=U) (W:=W) (p:=p) r) := by
  intro α d; let g := native c; let F := block S k p W r
  have hk := directGap S T k p W r hb
  have hj := directGap S U k p W r hb
  have hp := gauged G S.patch S.kernel p n hs ha
  have hd : 0 < d := hp.pos
  have he' : 4*(n+1:ℕ)*d ≤ α := hp.roomEnough.trans hp.roomTop
  have hα : α ≤ tier σ n := (half_lt_self (ordering hs n).1).le
  have hu : d ≤ tier σ n := by
    apply le_trans _ (he'.trans hα); push_cast; nlinarith [show 0 ≤ (n:ℝ)*d by positivity]
  have hw := priceBlock S hb.2.2 hs ha hW hd.le hu hb.1 p r k
  have hσ : α+n*d ≤ tier σ n := by unfold α at *; push_cast at *; nlinarith [show 0 ≤ (n:ℝ)*d by positivity]
  have hc0 : 0 ≤ stageCost G S.patch S.kernel p n A σ+1 := add_nonneg (stage_nn _ _ _ _ hs ha) zero_le_one
  have hc := (buoy (padded (freeTo G S T) hw) (padded (freeTo G S U) hw) hc0
    (stocks (freeTo G S U) (freeTo G S T) (suits G _ ht) F 0) hd.le hσ he)
  let Z := crest S k (T:=T) (U:=U) (W:=W) (p:=p) r
  have hH : Bundle (guides (ray G c)) (park g hearth d v) g (home S) (home S) Z (0,x) n α
      (nuts G S.patch S.kernel p n A σ) := hc.mono le_rfl (le_of_eq (by unfold nuts; ring))
  refine ⟨hH.smooth,gap_mixture (A:=whole S T k p W r) (B:=whole S U k p W r)
    (Shell.gap _ (A:=F 0) hk) (Shell.gap _ (A:=F 0) hj) he.1 he.2,?_ ,fun l h hh => ?_⟩
  · have ht := hH.bound [] (by simp)
    rw [zeroth] at ht; exact ht.reclaim
  rw [mul_one]; exact hH.bound _ hh

lemma roll (R : ℕ) {x : ℝ} (he : x ∈ Icc (0:ℝ) 1) :
    let α := tier σ n / 2; let d := width G S.patch S.kernel p n A σ
    let Z := crest S k (T:=T) (U:=U) (W:=W) (p:=p)
    let C := phasePrice G S.patch S.kernel n A σ
    let N := Real.exp (-(σ/4)*R)*(2*tagPrice 1 n C C)
    Bundle (guides (ray G c)) (park (native c) hearth d v) (native c) (home S) (home S) (Z all-Z (shorter R))
      (0,x) n α (3*N) := by
  intro α d Z C N; let g := native c
  let X := block S k p W all
  let Y := block S k p W (shorter R)
  let F := whole S T k p W all-whole S T k p W (shorter R)
  let H := whole S U k p W all-whole S U k p W (shorter R)
  have hp := gauged G S.patch S.kernel p n hs ha
  have hd : 0 < d := hp.pos
  have he' : 4*(n+1:ℕ)*d ≤ α := hp.roomEnough.trans hp.roomTop
  have hu : d ≤ tier σ n := by
    apply le_trans _ (he'.trans (half_lt_self (ordering hs n).1).le); push_cast; nlinarith [show 0 ≤ (n:ℝ)*d by positivity]
  have h1 := tail_block S hb.2.2 hs ha hW hd.le hu R p k
  have hN : 0 ≤ N := mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) (tag_nn (phase_nn _ _ _ hs ha) (phase_nn _ _ _ hs ha)))
  have hσ : α+n*d ≤ tier σ n := by unfold α at *; push_cast at *; nlinarith [show 0 ≤ (n:ℝ)*d by positivity]
  have hC : Alert (home S) v (H-F) 0 := Shell.tracks_difference _ _ (suits G _ ht) X Y _
  have hZ : Bundle (guides (ray G c)) (park g hearth d v) g (home S) (home S) (mixture F H)
      (0,x) n α (N+(N+N)) := buoy (pay_sub _ h1) (pay_sub _ h1) hN hC hd.le hσ he
  rw [show Z all-Z (shorter R)=mixture F H from ?_]; exact hZ.mono le_rfl (le_of_eq (by ring))
  ext1 y; simp only [Z, F, H, crest, mixture, castLift, stir, Pi.sub_apply,smul_sub]; abel
end train
end YM.FreeResolvent.Affine
