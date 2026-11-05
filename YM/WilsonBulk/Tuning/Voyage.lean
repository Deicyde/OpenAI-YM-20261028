import YM.WilsonBulk.Tuning.Upstream

/-!
# Initial Whispers (every period). Physical stencil Wilson-term with unit
 summit receipt. Future application uses actual `kinetic`, not a transverse
 projection of remainders of density. Costumes anchored at any Biosk
 meeting top primitive.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open Work.F08 RG Sheet Pert.Bulk Atelier
open PowerSeries (coeff constantCoeff)
variable {c n : Side} {G : Gauge} {B : Bed} {V : Text (Cloth G) 2} {η A C θ : ℝ} {p : Clip}
lemma top_regime (n : Side) (B : Bed) (G : Gauge) (hp : Floor B p n η C) (ht : B.diagonal.acts n=1) : Regime (audienceK G n (upstream G)) := by
  obtain ⟨he,-⟩:= upstream_flag _ _ _ B hp ht
  let U:=audienceK G n (upstream G); let K:=energyStub G n
  constructor
  · intro s b; apply PowerSeries.X_pow_mul_cancel (k:=2); rw [show (PowerSeries.X:Logbook G n)^2*submit _ U= submit (exposure (swivel s b)) (_*U) from ?_,he]
    rw [← ink_comp (luminous G n) ((swivel_jet ..).contDiffAt) (swivel_birth ..)]; apply congr_arg
    funext x; simp only [energyStub,Function.comp_apply, swivel_sign,energy_pull]
    simp [submit_X]
  intro k; apply PowerSeries.X_pow_mul_cancel (k:=2); unfold mountain; rw [← upper_code]
  let T:= upper (Pennant G n) (Needle G n)
  have hv {α : Type} (v : Pennant G n→Tape α) : PowerSeries.X^2*submit v (audienceK G n (upstream G))=submit v (ink K):= by rw [← he,map_mul,map_pow,submit_X]
  rw [hv,hv,← ink_comp (luminous G n) (pigment_jet k) (pigment_birth k),← ink_comp (luminous G n) T.contDiff.contDiffAt T.map_zero]; refine ink_of ((pigment_laid k).mono fun x hx=>?_)
  dsimp only [K,energyStub, Function.comp_apply] -- adjust
  rw [show signal G n _=_ from hx, Atelier.narrative,energy_gauge]

variable {P : Levels G} {H : Horizon P} {F : MapPrices}
lemma initial_whisper (X : ℕ) (h : H.Suffices F) : Whisper (upstream G) :=
  ⟨top_style G,top_free_stmt G,top_public G,fun n=>top_regime n (H.H X X) G (h.all X X le_rfl n) (h.top X n)⟩
lemma voyage_crest (h : H.Suffices F) (X : ℕ) : Crest (upstream G) (H.H X X) := by
  let v:=upstream G; let u:=summit G (H.H X X); let ξ:= H.H X X
  have hh := (h.rows X X le_rfl).2.1; have hG:= summit_public G (actionKernel_strip (F.alpha_pos _).le hh) (F.alpha_pos _)
  have hx (c : Side) := (upstream_flag _ G c ξ (h.all X X le_rfl c) (h.top X c)).2
  have hv (n : Side) : constantCoeff (volumeTape (Sheet.issue n v))=constantCoeff (volumeTape (Sheet.issue n u)) := by rw [show u= summit G _ from rfl,summit_tape G (F.alpha_pos _).le hh]; exact hx n
  have hp (k : Side) : Document (Sheet.issue k u):= hG.at_issue k (summit_style ..)
  have hq (k : Side) : Document (Sheet.issue k v):= Pamphlet.at_issue (top_public G) k (top_style ..)
  funext i; cases i
  · exact (top_free_stmt G _).trans (summit_hairless G _ _).symm
  rename_i i; let D:=cascade (1:Side); refine Proxy.uniq (D:=D) cascade_up ((top_public G 0 (i+1)).forever D) ((hG 0 _).forever D) (Eventually.of_forall fun k=>?_) (by omega)
  refine script_trust (hq (D k) |>.coherent 0 _) ((hp (D k)).coherent 0 _) ?_ ; rw [← rights (hq (D k)).cap, ← rights (hp (D k)).cap, PowerSeries.coeff_zero_eq_constantCoeff, hv (D k)]
lemma top_price (i : G.ColorIndex) (d) (hd : d≠0) : subdue i (upstream G d (1+1))=0:= by rw [upstream,chapters,if_neg (by omega),subdue_zero]
end YM.WilsonBulk.Parapet
