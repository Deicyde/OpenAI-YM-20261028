import YM.RG08.Germ.Foliage

/-! # Remainder-free action update at own grade, strict events

Does *not* consume/infer KT smoothing for post estimates. Prepare all
numeric isolated patch costs before recurrence. `shadow` here bulk-action
*predicted same-rank transfer* along chosen tree, not public Mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {L : Side} {P : Patch} {G : Gauge} {t : Train P.J} {ν : G.ColorIndex}
variable {n r e : ℕ} {κ : KernelChoices} {D : ChartRatio G} {F : Air G}

def luggage (i : G.ColorIndex) (P : Patch) (D : ChartRatio G) (k : KernelChoices) (e r : ℕ) :=
    -(if r=e+2 ∧ 0 < e then blot i P k.penalty r else 0)+(if r=e ∧ 0<e then gemL P.L (brimJ i D r) else 0)
lemma lenitive (Q : G.ColorIndex) (P : Patch) (D : ChartRatio G) (κ : KernelChoices) (e r) : Tunable (luggage Q P D κ e r) := by
  apply Tunable.add; swap
  · split; next h=> exact gem_tune _ _ (brim_tune ..).1
    exact Tunable.zero ..
  apply Tunable.neg; split; exact blot_sym ..; exact Tunable.zero ..
lemma nuts (i : G.ColorIndex) (P : Patch) (D : ChartRatio G) (κ : KernelChoices) (e r : ℕ) :
    awakening i P D κ.penalty F e r=luggage i P D κ e r-gemL P.L (F e r) := by unfold awakening luggage; abel

def feather {L : Side} (u : Pot G r) (Q : Cross L (Loc G 1) (Loc G 1)) := scrollL (gemL L u) (scan Q)

def scramble (i : G.ColorIndex) (P : Patch) (D : ChartRatio G) (κ : KernelChoices) (M : Row (Fink G P.L) (Fink G P.L))
    (Q : Cross P.L (Loc G 1) (Loc G 1)) (F : Air G) (e r) := - scrollL (luggage i P D κ e r + afterT (veiled M) (awakening i P D κ.penalty F) none 1 e r) (scan Q)
lemma division (i : G.ColorIndex) (P : Patch) (D : ChartRatio G) (κ : KernelChoices) (X : Repeated P.L) (w : Train P.J)
    (h : P.Branches κ G) {F : Air G} (hp : Gets F) (e r) :
    let M:=conditionalCov G X κ w
    let Q := coarseMean G X κ w
    strike i P D κ X w F e r=feather (F e r) Q + scramble i P D κ M Q F e r := by
  intro M Q
  have he : Whole M:= (conditional_truth G X κ w h).1
  have hs : Whole Q:= (he.prod (probe_recites G P κ|>.1.flipped)).weight _
  let U := awakening i P D κ.penalty F; have hu := Gets_awake P D κ i hp
  let S := upswell (veiled M) U none 1 e r; let T := afterT (veiled M) U none 1 e r
  have hE : Summable S := ((upswell_deck (veiled M) (veiled_whole he) _ (fun a b=> (hu.2 a b).1) hu.1 none 1).2 e r).1
  let H:=gemL P.L (F e r); let L:=luggage i P D κ e r
  have hf : Summable H:=(gem_tune _ _ (hp.2 e r).1.1).1
  have hh : S+H=L+T := by unfold S; rw [soothe]; change U e r + T + H = L+T; rw [show U e r=L-H from nuts ..]; abel
  change -scrollL S (scan Q)=scrollL H (scan Q) + -scrollL (L+T) (scan Q)
  rw [← hh,scroll_more hE hf (scan_whole hs)]; abel
lemma feather_step {F : Pot G r} (h : Summable F) {Q : Cross L (Loc G 1) (Loc G 1)} (hk : Whole Q) : feather F Q=flow F Q := by
  let A : Fin r→Row _ _ := fun _=> Q
  apply (scroll_tune ((gem_tune F L h).1) (scan_whole hk)).unique
      (score_tunable (ribbons_sum (grapes_summable L h) (fun _=>hk)))
  intro c; let g : Ratio c (c*L) := ⟨L,rfl⟩
  funext x
  rw [scroll_play (A:=scan Q) ((gem_tune F _ h).1) (scan_whole hk),show (scan Q).acts c*ᵥ x=_ from scan_at (G:=G) g Q x, gem_light F h g,lodge_f];
  rw [stanza_score (ribbons_sum (grapes_summable L h) (fun _=>hk))]; unfold stanza Tensor.diagonal; rw [ribbon_eval_all (grapes_summable L h) (fun _=>hk),grapes_rec g _ (h)]; rfl
end YM.RG08
