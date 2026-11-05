import YM.RG08.Loom.Slant
/-!
# Signed calculation on *full* probes, not vacuum sector identity
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent Profiles PertExtension.Chart
open Planned.PrimaryIntegral295.Place
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {c f L : Side} {G : Gauge}
variable {M : Matrix (Body 1 f) (Body 1 c) ℝ} {v w : ℝ→Link G c} {n h j τ e r : ℕ} {k : KernelChoices} {D : ℕ}{R : ℝ} {φ φ' : Exam D}
variable {U U' : BoardU D R G} {V : ℕ→ Config G f→ℝ}{F F' : Air G} {B K : FreeResolvent.FaceRow} {σ : ChartRatio G} {o o' : Site c} {i : G.ColorIndex} {p : Option Side} {P : Patch} {X : Repeated P.L} {w' : Train P.J}

def twisting (s : Signed) (φ : Exam D) : Exam D := ⟨φ.val ∘ (Ortho.motion s.ortho), (Scores.score D φ).comp (Ortho.motion s.ortho).contDiff⟩
def Honor (s : Signed)(U U' : BoardU D R G)(m : Side): Prop := ∀ i : Site m,∀ φ : Exam D,DiscSpin s (s.act i) i (fun e r=> plug φ R ∘ U e r) (fun e r=> plug (twisting s φ) R ∘ U' e r)
lemma seat_twists (s : Signed)(x : Cover): seat (s.act x)= Ortho.motion s.ortho (seat x) := by
  change _=Ortho.move s.ortho _; rw [s.ortho_move]; ext i; simp; obtain ⟨a,rfl⟩:= s.perm.surjective i; rw [s.act_at,s.act_at]; split <;> simp [Planned.PrimaryIntegral295.Place.seat]
lemma leaf_twists (s : Signed)(i : Site P.L)(φ : Exam D): twisting s (Pages.roll (spinner (s.act i)) (P.L.val:ℝ)⁻¹ φ)= Pages.roll (spinner i) (P.L.val:ℝ)⁻¹ (twisting s φ) := by
  apply Subtype.ext; funext x
  change φ.val (spinner (s.act i)+(P.L.val:ℝ)⁻¹ • (Ortho.motion s.ortho x)) = φ.val (Ortho.motion s.ortho _)
  simp only [spinner,Ratio.lift_signed_of_odd P.odd_side,seat_twists,map_add,_root_.map_smul]
lemma pays_leaf (k : KernelChoices) (hm : f.val=c.val*P.L.val) (A : BoardU D R G) (T : BoardU D R G) (i : Site P.L) (o : Site c)(φ : Exam D) {s : Signed}(h : Honor s A T f) :
    let S := linked P k c f hm
    DiscSpin s (S.ratio.assemble (s.act o,s.act i)) (S.ratio.assemble (o,i))
      (fun e r=> plug (Pages.roll (spinner (s.act i)) (P.L.val:ℝ)⁻¹ φ) R ∘ A e r)
      (fun e r=> plug (Pages.roll (spinner i) (P.L.val:ℝ)⁻¹ (twisting s φ)) R ∘ T e r) := by
  intro S; rw [S.ratio.assemble_signed P.odd_side, ← leaf_twists s i φ]; exact h (S.ratio.assemble (o,i)) (Pages.roll _ _ _)

-- extraction simpler than gauge: erase polys using literal slot grade rake.
lemma attend (he : f.val=c.val*P.L.val) (hp : LocalRatio σ) (hk : P.Branches k G)
    (hB : Whole B) (hM : ∀ m,(B.acts m).IsSymm)
    (hX : Inputs (linked P k c f he) M ((pink k.penalty w').acts f) (B.acts c))
    (hV : Faithful (quad G (YM.RG08.hessian (pink k.penalty w'))) F f)(hF : Gets F)(ht:Halt F)(hU : ∀ i j, Tidy (U i j))(hU' : ∀ i j,Tidy (U' i j))(hP:Fits τ U)(hP':Fits τ U')(hO:1/2 ≤ R)(h : ℕ)
    (hz : Parade f τ U)(s : Signed)(hs: Honor s U U' f) : Honor s (filament P k w' σ i X F (some c) U τ h) (filament P k w' σ i X F (some c) U' τ h) c := by
  let S:=linked P k c f he; let T:= X.forest S.ratio; let p := (s.actEquiv (R:= Per P.L)).toEquiv; let A := filament (R:=R) (D:=D) P k w' σ i X F (some c)
  let κ : S.Choices:= Classical.arbitrary _
  intro o φ u r y
  let Z (i:Site P.L):=fun a r=> plug (Pages.roll (spinner i) (P.L.val:ℝ)⁻¹ φ) R∘ U a r
  let L:=fun a r=> plug φ R∘ A U τ h a r; let H:=fun a r=> plug (twisting s φ) R∘ A U' τ h a r
  let Y v a:= large (s.act o) (τ+a) (L a) v; let W v a:= large o (τ+a) (H a) v
  have he' (x : Link G c) : Y x u = W (orderTurn s x) u := by
    obtain ⟨V,hv⟩:= costumed hV (τ+u)
    choose Q hQ using fun (j:Site P.L) n=> shelved (p:=n) (show Shore (S.ratio.assemble (s.act o,j)) τ (Z j) from hz (Pages.roll (spinner j) _ φ) (S.ratio.assemble (s.act o,j))) (show τ ≤ τ+u+τ+n by omega) (fun i j=> Tidy.map _ (hU i j))
    let B (a: Site P.L) i:= Q (p a) i∘pull s⁻¹ 0
    have hh (j:Site P.L) n:= rotates_shell s (hQ (p j) n) (pays_leaf _ he U U' j o φ hs) (fun a b=> Tidy.map _ (hU' a b))  
    obtain ⟨e,hE⟩:= sails_signed S G T (v:=fun t:ℝ=>x) (w:=fun _=>orderTurn s x) (W:=Q) (W':=B) (κ:=κ) s hk (fun i=>(hv i).word) (Eventually.of_forall (fun t=> by rw [← map_smul]; exact (flip_links ..).symm)) (fun i j=>(hh i j).toShell) p
      (fun i a=> Eventually.of_forall (fun t=> congr_arg (Q (p i) a) ((signedWalk G f s).symm_apply_apply t))) h (τ+u) τ
    have hA := lank he hp hk hB hM hX (i:=i) (X:=X) hv hF ht hU hU' hP hP' hO analyticAt_const analyticAt_const Q B hQ hh e κ hE
    have hN:Fit (u+1) (peval (Y x) u) (peval (W (orderTurn s x)) u):= hA
    simpa only [le_refl,if_true] using aspiredV hN (Aspiration.polynomial _ _) (Aspiration.polynomial _ _) (le_refl u)
  have hK:= (conditional_truth G X k w' hk).1; have hM: Whole (coarseMean G X k w') := (hK.prod ((probe_recites G P k).1.flipped)).weight _
  have hA:=Gets_awake P σ k i hF; have hK' : ∀ U' : BoardU D R G,(∀ i j, Tidy (U' i j)) → Fits τ U' → Fits τ (A U' τ h) ∧ (∀ i j,Tidy (A U' τ h i j)) := fun U' hU hP=> filops_charge hP (fun i j=>(hU i j).pens) hO P.odd_side hK hM hA.1 (fun i j=> (hA.2 i j).1)
  rcases le_or_gt r (τ+u) with he|he
  · have H₁ : (fun t:ℝ=>Y (t•y) u)=(fun t=> W (t • orderTurn s y) u) := funext fun t=> (he' _).trans (congr_arg (fun x=>W x u) (map_smul ..))
    unfold Y W at H₁; rw [large_past,large_past] at H₁
    have hp:=aspiredV (Fit.supply (Filter.EventuallyEq.of_eq H₁) (τ+u+1)) (Aspiration.polynomial _ _) (Aspiration.polynomial _ _) he
    change (if r≤τ+u then _ else _)=_ at hp; simpa only [he,↓reduceIte] using hp
  obtain ⟨Q,T⟩:= hK' U hU hP
  have hL:Fits τ L:= Fits.echo Q φ; have hH : Fits τ H:= Fits.echo (hK' U' hU' hP' |>.1) _
  change rootSong (L u r) c _ _=rootSong (H u r) c _ _; rw [not_ne_iff.mp (mt (hL _ _) (not_le.mpr he)),not_ne_iff.mp (mt (hH _ _) (not_le.mpr he)),root_zero,root_zero]; rfl
end YM.RG08.Loom
