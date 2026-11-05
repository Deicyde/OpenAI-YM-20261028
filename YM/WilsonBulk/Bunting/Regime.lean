import YM.WilsonBulk.Bunting.Priority

/-!
# Protecting exact angular and gauge invariance of complete outputs

Use multiple-period descent after winding images pruned. Preserve at every
power (truncated stamps supported). Applies to SELF outputs including rank1.
Doesn't assert interpolation/exponent IR match. A meaningful norm-coefficient
predicate will also project/rank-resolve low moments by generator (later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open RG Sheet Pert.Bulk Atelier Tree Hallmark AnalyticNext.QuarticMatch.Sheets
variable {G : Gauge} {c f : Side} {B Q : Bed} {P : Patch} {K : KernelChoices} {T : Model P K} {J : ChartRatio G}
variable {α β : Type} {I : Library G}

structure Regime (I : Tape (Pennant G c)) : Prop where
  spins (s : Signed) (b : Site c) : Spins s b I I
  dance : Dances I
abbrev Costume (I : Library G) := ∀ n,Regime (audienceK G n I)
-- all coefficients incl nonlinear gauge BEFORE resetting, even period 1 (ambiguous geometry but periodic identities hold).
structure Whisper (I : Library G) : Prop where
  style : Document I
  cash : Cashless I
  palm : Pamphlet I
  guns : Costume I
-- future strict normalization predicate tracks affine-null tickets; `Gains`
abbrev Crest (I : Library G) (B : Bed) := I 0=summit G B 0
lemma Crest.lead (h : Crest I B) (_p : Pamphlet (summit G B)) (c : Side) (hp : volumeTape (issue c (summit G B))=grains (matrixK G c B)) : Steps 1 (audienceK G c I) (grains (matrixK G c B)) := by
  intro i hi; rw [Nat.eq_zero_of_le_zero (by omega : i≤0), ← hp, audienceK,tape_power,tape_power]; unfold capsule Sheet.issue; rw [h]

variable (h : Passage J B Q T)
include h in
lemma flare_regime {V : Library G} (hI : Whisper V) (he : Crest V B) (hQ : Bid.Larger (G:=G) (draftAt P K c)) : Regime (volumeTape (torch J T B Q V c)) := by
  let S:=draftAt P K c; let F:= reality S T; let R : Coursing F.Free S:= ⟨F,Equiv.refl _⟩; obtain ⟨σ,hs,C,hC,hx⟩:= h.spectral; let t:S.Choices:=Classical.arbitrary _
  have hp := flame_energizes J B V T hs.le hx hI.palm hI.style (he.lead h.summit_here _ (h.auditions _)) hQ h.toll t R rfl
  obtain ⟨x,hy,ht⟩:= h.chairs (trimSide P c)
  have hh : volumeTape (torch J T B Q V c)=pressurize Q (volumeTape (flameI J T B V c)) := by unfold torch; rw [tape_minus,h.auditions_next]
  have hv := h.choice c; let E:=hI.guns (trimSide P c)
  rw [hh]
  exact ⟨fun s b=> spins_post s b hQ hv hy ht h.toll hp hp E.dance (E.spins s _), dances_post hQ hv hy ht h.toll hp E.dance⟩

def cascade (c : Side) (i : ℕ) : Side := ⟨(i+1)*c.val, Nat.mul_pos (by omega) c.property⟩
lemma cascade_div (i : ℕ) : c.val∣(cascade c i).val := dvd_mul_left ..
lemma cascade_up : Tendsto (fun i : ℕ=> (cascade c i).val) atTop atTop := tendsto_atTop_mono
  (fun i=> (show i≤(i+1) by omega).trans (Nat.le_mul_of_pos_right _ c.property)) tendsto_id

section lodgment
variable (hd : c.val∣ f.val)
def mantle (G : Gauge) : Interface G c →L[ℝ] Interface G f := socket (harbor (Cloth G) hd)
lemma mantle_signal (x : Interface G c) : signal G f (mantle hd G x) = copies hd (signal G c x):= rfl
variable [Fintype β]
lemma exposure_plus (x : Tabletop β→ Interface G c) : exposure (mantle hd G ∘ x)=exposure x ∘ (harbor _ hd) := rfl
lemma enjoy (b : Site c) (s : Signed)
    {T : Tape (Pennant G f)} (hp : Regime T) {t : Tabletop β→ Site c→G.El} (hq : Army t 0) {k : G.El} (ht : t 0=Function.const (Site c) k)
    {u v : Tabletop β→Interface G c} (hv : ContDiffAt ℝ ω u 0) (hh : u 0=0) (hV : ContDiffAt ℝ ω v 0) (h' : v 0=0) (h : ∀ᶠ z in 𝓝 0, signal G c (v z)= Lattice.gauge (t z) (pull s b (signal G c (u z)))) :
    submit (exposure v ∘ harbor (Cloth G) hd) T= submit (exposure u ∘ harbor (Cloth G) hd) T := by
  let U:= mantle hd G; let b' := pin hd b; rw [← exposure_plus hd v,← exposure_plus hd u]; refine rhythm s b' (t:=fun z=> t z∘ project hd) (fun i=> hq _) (by rw [ht]; rfl) (U.contDiff.contDiffAt.comp _ hv) (U.contDiff.contDiffAt.comp _ hV) (by rw [Function.comp_apply,hh,map_zero]) (by rw [Function.comp_apply,h',map_zero]) hp.dance (hp.spins s b') (h.mono fun z hz=> ?_); dsimp only [Function.comp_apply]; rw [mantle_signal,mantle_signal,hz,pull_copies,gauge_copies,pin_site]
variable {hd}
-- full-context tapes through any finite expansion demand
lemma priced_bolts {D : ℕ→Side} {K : ∀ i,circular G (D i)} (he : ∀ i,c.val∣ (D i).val)
    (hI : dean D K I) (b : Site c) (s : Signed) (p : ∀ᶠ i in atTop,Regime (G:=G) (volumeTape (K i)))
    {t : Tabletop β→ Site c→G.El} (hq : Army t 0) {k : G.El} (ht : t 0=Function.const (Site c) k)
    {u v : Tabletop β→Interface G c} (hv : ContDiffAt ℝ ω u 0) (hh : u 0=0) (hV : ContDiffAt ℝ ω v 0) (h' : v 0=0) (h : ∀ᶠ z in 𝓝 0, signal G c (v z)= Lattice.gauge (t z) (pull s b (signal G c (u z)))) :
    submit (exposure v) (audienceK G c I)=submit (exposure u) (audienceK G c I) := tribute _ _ he hI (p.mono fun i pi=> enjoy (he i) b s pi hq ht hv hh hV h' h)
omit [Fintype β] in
lemma regime_renews {D : ℕ→Side} {K : ∀ i,circular G (D i)} (he : ∀ i,c.val∣ (D i).val)
    (hI : dean D K I) (p : ∀ᶠ i in atTop, Regime (G:=G) (volumeTape (K i))) : Regime (audienceK G c I) := by
  let u:= upper (Pennant G c) (Needle G c); constructor
  · intro s b; apply Eq.trans (priced_bolts he hI b s p (t:=fun _=>1) (u:=id) (v:=swivel s b) (k:=1) (Army.park _ _) rfl contDiffAt_id rfl (swivel_jet ..).contDiffAt (swivel_birth ..) (Eventually.of_forall fun z=> Eq.trans (swivel_sign ..) (turn_person _).symm)) ?_
    rw [exposure_id, submit_id]
  intro k; have he:= priced_bolts he hI 0 1 p (u:=u) (v:=pigment c k) (t:=curtainK c k ∘ lower _ _) (weatherK k (lower (Pennant G c) (Atelier.Needle G c)).contDiff.contDiffAt) (k:=k) (by rw [Function.comp_apply,map_zero,curtainK_zero]) u.contDiff.contDiffAt (map_zero _) (pigment_jet k) (pigment_birth k) ((pigment_laid k).mono (fun x hx=> by rw [pull_id]; exact hx)); unfold u at he; simpa only [upper_code,mountain] using he
end lodgment
include h in
lemma whispers_post (hI : Whisper I) (he : Crest I B) : Whisper (pressureI J T B Q I) :=
  ⟨pressure_style _ _ _ _ I hI.style, pressure_cash _ _ _ _ _, h.hears hI.palm, fun n=> regime_renews (D:=cascade n) cascade_div (h.peers cascade_up hI.palm) ((h.perimeter (D:=cascade n) cascade_up).mono (fun _ hi=>flare_regime h hI he hi))⟩
end Parapet
end YM.WilsonBulk
