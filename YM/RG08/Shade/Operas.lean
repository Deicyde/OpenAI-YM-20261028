import YM.RG08.Shade.Ports
/-!
# Formal step of a rooted untested source. Includes field-independent channels
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Shade
open Function Filter Set Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Scores.Pages Matrix Push.AbsoluteSums
open scoped Topology ContDiff Classical
variable {α β ι : Type} {D h e τ r k : ℕ} {L c f : Side} {G : Gauge} {i : Site L} {p : Option Side} {m : Site c} {R w η σ A B : ℝ}
-- τ = slot allowance, h = engineering horizon
abbrev BoardU (D : ℕ) (R : ℝ) (G : Gauge) := Screed (Voice D R) (Loc G 1)
abbrev EnvelopeU (D : ℕ) (R : ℝ) (G : Gauge) (r : ℕ) := Rooted (Voice D R) (Loc G 1) r
-- pick paths in full finite; branch-general

def raysF (p : Site L) (U : EnvelopeU D R G r) := spring (shiftP p (fun i=> readdress (U i) p)) (skylight _ (Loc G 1))
def reelF (p : Site L) (h : ℕ) (U : BoardU D R G) (e r:ℕ) := ((L.val:ℝ)^h / Fintype.card (Site L)) • raysF p (U e r)
-- entire input is unnormalized density times this mark exp in separate routes.
def cream (h : ℕ) (U : BoardU D R G) (L : Side) (e r:ℕ) := ∑ p: Site L, reelF p h U e r

def filop {L : Side} (A : Row (Fink G L) (Fink G L)) (Q : Row (Fink G L) (Loc G 1))
    (E : Canticle (Park G L)) (p : Option Side) (τ h : ℕ) (U : BoardU D R G) (e r : ℕ) := spring (washed τ p (veiled A) E (cream h U L) e r) (scan Q)

variable {U : BoardU D R G}
variable {V F : EnvelopeU D R G r} {K : Row (Fink G L) (Fink G L)} {Q : Row (Fink G L) (Loc G 1)}
lemma skylight_ok : Whole (skylight (Co L (Loc G 1)) (Loc G 1)) := ⟨_,_,one_pos,skylight_price⟩
lemma rays_print (hp:Pens V) (hx : 1/2 ≤ R) (he : Odd L.val) (i : Site L) : Pens (fun b=>readdress (V b) i) := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun j=> (read_scores he hx i (V j)).1) hp
lemma rays_tidied (hp : Pens V) (hx : 1/2 ≤ R) (he : Odd L.val) (i : Site L) : Tidy (raysF i V) := spring_tidy (shifted i (rays_print hp hx he i)) skylight_ok
lemma rays_lit (hp : Lit V w A) (hx : 1/2 ≤ R) (he : Odd L.val) (i : Site L) (hw : 0≤η)(hη:η≤L.val*w) :
    Lit (raysF i V) η ((Fintype.card (Park G L):ℝ)^r*(Real.exp (4*η)^r*A)) := by
  have hh : Lit (fun b=>readdress (V b) i) w A := budget_mono hp (fun b=>mul_nonneg (ling_pos _ _).le (norm_nonneg _)) (fun b=> mul_le_mul_of_nonneg_left (read_scores he hx i (V b)).1 (ling_pos _ _).le)
  have h := spring_receipt (shift_print i hh hw hη) hw zero_le_one (Q:=skylight _ (Loc G 1)) skylight_price
  rw [one_pow,mul_one] at h; exact h
lemma rays_sub (hp:Pens V) (hv:Pens F) (hx : 1/2 ≤ R) (he : Odd L.val) (i : Site L) : raysF i (V-F)=raysF i V-raysF i F := by
  have hz (u v : Voice D R): readdress (u-v) i=readdress u i-readdress v i := by simp only [readdress,he,hx,true_and, ↓reduceDIte]; rfl
  let f (V : EnvelopeU D R G r) b := readdress (V b) i
  unfold raysF; change spring (shiftP i (f (V-F))) _=_; rw [show f (V-F)=f V-f F from funext fun b=>hz ..,show shiftP i (f V-f F)= shiftP i (f V)-shiftP i (f F) from Pens.tub_sub _ (rays_print hp hx he _) (rays_print hv hx he _), spring_sub (shifted i (rays_print hp hx he _)) (shifted i (rays_print hv hx he _)) skylight_ok]
lemma rays_zeros (hx : 1/2 ≤ R) (he : Odd L.val) (i : Site L) : raysF i (0:EnvelopeU D R G r)=0 := by simpa only [sub_self] using rays_sub (Pens.zero _ _ : Pens (0:EnvelopeU D R G r)) (Pens.zero _ _) hx he i
lemma creamy (h : ℕ) (L : Side) (hp : Fits τ U) (he : ∀ i r,Pens (U i r)) (hx : 1/2≤R) (hl : Odd L.val):
    Fits τ (cream h U L) ∧ ∀ i r,Tidy (cream h U L i r) := by
  refine ⟨?_,fun i r=> Tidy.additions fun p _=> (rays_tidied (he i r) hx hl p).scale _⟩
  intro i r hg; contrapose! hg; unfold cream reelF
  simp_rw [show U i r=0 from not_ne_iff.mp (mt (hp i r) (not_le.mpr hg)),rays_zeros hx hl,smul_zero,sum_const_zero]
lemma filops_charge {S : Canticle (Park G L)} (hp : Fits τ U) (he : ∀ i r,Pens (U i r)) (hx : 1/2≤R) (hl : Odd L.val)(ht : Whole K)(hz : Whole Q)(hg : Decked S)(hS : ∀ i k,Tunable (S i k)) :
    Fits τ (filop K Q S p τ h U) ∧ ∀ e r,Tidy (filop K Q S p τ h U e r) := by
  have ⟨h₁,h₂⟩:= creamy h L hp he hx hl
  have ⟨hw,H⟩:= washed_duty (s:=p) (veiled_whole ht) hS hg h₂ h₁
  refine ⟨fun i r hF=> by_contra (fun hT=> hF ?_),fun i r=> spring_tidy (H i r|>.pens) (scan_whole hz)⟩
  unfold filop; rw [show washed _ _ _ _ _ i r=0 from not_ne_iff.mp (mt (hw i r) hT)]; exact spring_zero (scan_whole hz)
-- plug test α (=continuous evaluation)
def plug (g : Exam D) (R : ℝ) : Voice D R →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (sheet D R g)
lemma rays_present (g : Ratio c f) (p : Site g.count) (v : Alley G g) (i : Site c) (h : Pens V)
    (he : 1/2≤R) (hp : Odd g.count.val) (φ : Exam D) : rootSong (plug φ R ∘ raysF p V) c i v =
        rootSong (plug (roll (spinner p) (g.count.val:ℝ)⁻¹ φ) R ∘ V) f (g.assemble (i,p)) (fineL G g v) := by
  let U b:= readdress (V b) p
  have hx : Pens U := rays_print h he hp p
  let F := plug φ R ∘ U
  unfold raysF
  change rootSong (plug φ R ∘ spring (shiftP p U) _) _ _ _=_
  rw [spring_echo _ (shifted p hx) skylight_ok, show plug φ R ∘ shiftP p U=shiftP p F from Pens.echo_pool _ hx _,spring_tell _ (shifted p (hx.shaped _)) skylight_ok,rootSong,Tensor.diagonal, shifts F g p i _ (hx.shaped _)]
  rw [show F=_ from (funext fun b=> (read_scores hp he p (V b)).2 φ : F=plug (roll (spinner p) _ φ) R ∘ V)]; change _=stitch _ f _ _
  congr 1; funext x j; change ((skylight _ (Loc G 1)).acts c *ᵥ v) (splitCo g _ j) = _; rw [skylight_in]; rfl

lemma cream_present (g : Ratio c f)(v : Alley G g) (i : Site c) (h : ℕ) (e : ℕ) (r : ℕ)(φ : Exam D) (hp : Pens (U e r)) (hR : 1/2≤R) (hh : Odd g.count.val) :
    rootSong (plug φ R ∘ cream h U g.count e r) c i v=
        ∑ j:Site g.count,((g.count.val:ℝ)^h/Fintype.card (Site g.count))*rootSong (plug (roll (spinner j) (g.count.val:ℝ)⁻¹ φ) R ∘ U e r) f (g.assemble (i,j)) (fineL G g v) := by
  unfold cream; rw [graft, root_sum i univ (fun p => plug φ R ∘ reelF p h U e r) (h:=fun z _=> (((rays_tidied hp hR hh z).pens.scale _).shaped (plug φ R))), Finset.sum_apply]
  apply Finset.sum_congr rfl; intro j _; rw [show plug φ R ∘ reelF j h U e r=((g.count.val:ℝ)^h/Fintype.card (Site g.count)) • (plug φ R ∘ raysF j (U e r)) from funext fun i=>by simp [reelF],root_scale i ((rays_tidied hp hR hh j).pens.shaped _) _, Pi.smul_apply,smul_eq_mul,rays_present g j v i hp hR hh]

lemma Fits.echo (hp : Fits τ U) (φ : Exam D) : Fits τ (fun i r=> plug φ R ∘ U i r) := fun i r he=> hp i r (fun H=> he (by dsimp only; rw [H]; ext; simp))
lemma projected_out {K : Row (Fink G L) (Fink G L)} (he : Odd L.val) (hR : 1/2≤R) {S : Canticle (Park G L)} (hp : Fits τ U) (ht : ∀ i r,Pens (U i r))(hK:Whole K)(hM:Whole Q)(hg:Decked S)(hS:∀ i k,Tunable (S i k)) (φ : Exam D) (G' : Site c) (x : PAC (Loc G 1) c) (h : ℕ) (e : ℕ):
   large G' (τ+e) (fun r=> plug φ R ∘ filop K Q S p τ h U e r) x=large G' (τ+e) (washed τ p (veiled K) S (fun i j=> plug φ R ∘ cream h U L i j) e) ((scan Q).acts c *ᵥ x) := by
  obtain ⟨h₁,h₂⟩ := creamy h L hp ht hR he; unfold large
  rw [Finset.sum_apply,Finset.sum_apply]
  apply sum_congr rfl; intro i _
  unfold filop; have hP := (washed_duty (s:=p) (veiled_whole hK) hS hg h₂ h₁).2 e i
  dsimp only; rw [spring_echo _ hP.pens (scan_whole hM),spring_tell _ (hP.pens.shaped _) (scan_whole hM),wash_map _ (veiled_whole hK) hS h₂]

end YM.RG08.Shade
