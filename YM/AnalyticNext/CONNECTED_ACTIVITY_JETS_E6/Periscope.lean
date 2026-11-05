import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Dryland
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orb

/-!
# Remote coherence of μ under all derivatives

May compute outside angular domain. **Every** physical comparison uses a
funded T; don't assume Health for entire interpolating ball when P wrappable;
just near 1. At all-small probe keep Y blank but forest never changes. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen Frond Gate Scroll Vine Tablet Metric Hues
variable {v z r Q s y η γ W w : ℝ} {j m : ℕ} {U : E → Config G c} {x : E}

def message (X : Coat T F) (p : Mention c f) := strain X p.1 p.2 (voltage X)

/-- `Aim` for every comparison required at a step. Width used from X
kept, not buying fresh history. Comes from Ledgered. -/
def Tent (P : Teller G) (L : Side) (x v η r Q Y : ℝ) (T : Tube G S) := ∀ (F : Forest S.ratio) (X : Coat T F),
    X.x=x → X.width=v → X.manifest → Port P L η r Q Y X

lemma passage (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) {V : ℝ → ℝ} (w : ℝ)
    (h : Rate G L (-(1/2)) V) (hv : ∀ᶠ x in atTop,0≤V x) {η r Q : ℝ} (Y : ℝ) (hT : Torch η r Q) : ∃ c X : ℝ→ℝ,
    Rate G L (-1) c ∧ Rate G L (1/2) X ∧ ∀ᶠ s in atTop, ∀ (c' f:Side) (S : StepData c' f) (T : Tube G S),
      S.patch=D → Works P L s S T→ Stamp T → Tent P L s w η r Q Y T →
        ∀ (F : Forest S.ratio) (p : Mention c' f) (W : Coat T F), W.x=s → W.width=w → ∀ x:ZipP G c' f,
         ‖x‖ ≤ V s → Brush j (c s) (X s) (fun v=> message (dry W v) p) x := by
  obtain ⟨d,hd,H₁⟩:= probe_window G L
  let t:= fun x=> d*mist G L x; let B x:= V x+3*t x
  have ht := (mist_rate G L).mul_left d; have hB: Rate G L (-(1/2)) B:= h.add (ht.mul_left 3)
  have he : ∀ᶠ s : ℝ in atTop, 0≤B s := by filter_upwards [hv,softly G L] with s hs hh; unfold B t; have hz:=hh.1; positivity
  have hX : Rate G L (1/2) (fun x=> (t x)⁻¹) := by simpa only [t,mist,_root_.mul_inv_rev,inv_inv] using!
    (Rate.mul_right (Rate.power (G:=G) (L:=L) (a:=1/2)) d⁻¹)
  obtain ⟨C,hC,h₂⟩:= abridge P L D hD (j+3) (by omega) hB he hT
  obtain ⟨E,hE,h₃⟩:= pressure_mean P D hD L η r Q Y hT
  refine ⟨_,_, recover_price ht hB hE hC (by norm_num) hX, hX,?_⟩
  filter_upwards [softly G L,hv,ht.below (by norm_num) 1 zero_lt_one,room G P L,H₁,h₂,h₃] with
    x hp hv hh hr hq hz H c f S T hd' ht hx hl F p W heq hy x' hv'
  subst x
  let A := W.x; let v i (x:ZipP G c f):= message (dry W x) i
  have ht' : 0<t A := mul_pos hd hp.1
  have hk : 3*t A ≤ B A := le_add_of_nonneg_left hv
  have hR:=hr c f S T ht
  have hh' (x:ZipP G c f) (he: x∈closedBall 0 (B A)) : Brush (j+3) (C A) 1 (v p) x :=
    hz c f S T hd' ht F W rfl (hl F W.blank rfl hy (W.bowed (temp_nonneg _))).sails.scale p x (mem_closedBall_zero_iff.mp he)
  have hm (x:ZipP G c f) (he : x∈closedBall 0 (3*t A)) : ‖v p x‖ ≤ E A := by
    let V:=dry W x
    have hx' i : Clean V.V V.x i (radiusB V.x) := hq c x.1 ((le_max_left ..).trans (show max _ _ ≤ _ from mem_closedBall_zero_iff.mp he)) i
    have hM : V.manifest := by
      ext v; change v∈ (∅:Support _) ↔ _; simp only [Finset.notMem_empty,false_iff]; exact hx' v v (by simp)
    unfold v message; change ‖strain V p.1 p.2 (voltage V)‖ ≤ _
    rw [← agrees_all V hR hM, ← strains V hR hM _ _ _ (show V.selected _ _ from W.blank_all _ _)]
    apply (H _ _ _ _ hd' ht.length_eq hx F V rfl (hl F V rfl hy hM).sails hM).2 p
    exact W.blank_no (root S p) (30*V.B)
  have ho : (0:ZipP G c f)∈closedBall 0 (3*t A) := mem_closedBall_self (by positivity)
  apply (ascend (k:=j+3) (by omega) ((norm_nonneg _).trans (hm _ ho)) ht' ((le_abs_self _).trans hh) hk ((hh' 0
    (closedBall_subset_closedBall hk ho)).nonneg) hh' hm x' (mem_closedBall_zero_iff.mpr ?_)).smaller (by omega)
  exact hv'.trans (le_add_of_nonneg_right (by positivity : 0 ≤ 3*t A))

private lemma tides (X : Coat T F) (p : Room P S T X.x) (e : ZipP G c f) (i : Mention c f)
    (h : ¬Inside (root S i) X.seeds (30*X.B)) (he : AgreeNear id (root S i) (24*X.B) X.V (increment 1 e.1)) :
    message X i=message (dry X e) i := by
  let o:=root S i; let Z:=dry X e
  have hh : Zone X Z o (24*X.B) := by
    refine ⟨rfl,rfl,rfl,fun z hz=> ?_,fun _ _ => rfl,he, fun _ _=>rfl, fun _ _=>rfl⟩
    refine iff_of_false (fun hg=> h ?_) (fun hg=> X.blank_no z 0 (halo_subset _ _ hg))
    exact Lattice.halo_spec.mpr ⟨z,hg,by rw [separation_comm]; change separation o z ≤30*X.B; omega⟩
  refine local_strain p hh i rfl (by omega) (voltage X) (voltage Z) (fun i hi _=>local_voltage p
    (hh.tune_down (q:=atEdge S i) (b:=17*X.B) (by unfold distAt at hi; omega)) i rfl le_rfl)

lemma rain (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) {V : ℝ → ℝ} (w γ W : ℝ)
    (h : Rate G L (-(1/2)) V) (hv : ∀ᶠ x in atTop,0≤V x) {η r Q : ℝ} (Y : ℝ) (hT : Torch η r Q) : ∃ C : ℝ→ℝ,
    Rate G L (-1) C ∧ ∀ᶠ s in atTop, ∀ (c' f:Side) (S : StepData c' f) (T : Tube G S),
      S.patch=D → Works P L s S T→ Stamp T → Tent P L s w η r Q Y T → ShellAccess S G s W w γ →
        ∀ (F : Forest S.ratio) (p : Mention c' f) (X : Coat T F), X.x=s → X.width=w →
        ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c') (x:E), Mode U x j (V s) →
        (vary X (U x)).manifest → ¬Inside (root S p) X.seeds (30*X.B) → Brush j (C s) 1 (fun v=> message (vary X (U v)) p) x := by
  obtain ⟨B,hB,hq⟩:= base_ray P L j h hv
  obtain ⟨A,c,hA,hc,hP⟩:= passage P L D hD j w hB (hq.mono fun x hx=> hx.1) Y hT
  refine ⟨_,parseRate j hA (hB.add hB) (by norm_num) (show Rate G L (- -(1/2)) _ by rw [neg_neg]; exact hc),?_⟩
  filter_upwards [hq,hP,room G P L] with x Hp H hh c f S T he ht ha hx hV F p X hX hw E _ _ U v hΥ hM hY
  subst x
  have hr := hh c f S T ht
  let o:=root S p; let W q:= vary X (U q)
  obtain ⟨z,b,hE,hF⟩ := Hp.2 _ _ S T ht E U v (24*X.B) o hΥ (by unfold Coat.B; omega)
    ((clean_far _ (U v) hM hY).shrink (by change separation o o+_≤_; rw [separation_self]; have hh:100≤X.B:=hr.sight.1; omega))
  let g i := (b i,(0:Directions G f))
  have hG := (scaled (Brush.pair hE ((Brush.certified zero_le_one (0:Directions G f)).climb (by rw [norm_zero]; exact Hp.1) le_rfl))
    (H c f S T he ht ha hx F p (sluice (W v) z) rfl hw (g v) (max_le hE.bound (by change ‖(0:Directions G f)‖≤_; rw [norm_zero]; exact Hp.1)))).trim
  let M:= (G.adjoint (z o)⁻¹).toContinuousLinearMap
  have hb:= hG.report M (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by rw [one_mul]; exact (G.norm_adjoint _ _).le))
  rw [one_mul] at hb; refine hb.shimmy ?_
  filter_upwards [hF] with i hi
  let p':= sluice (W i) z
  have hp : message (W i) p=M (message p' p) := by
    have hk := hw.symm ▸ hV
    rw [message,message, (fastens (W i) ht.funds hk z).2.2,reroot (W i) ht.funds hk z]; change _= G.adjoint _ (G.adjoint (z o) _)
    rw [← G.adjoint_mul, inv_mul_cancel,G.adjoint_one]
  exact hp.trans (congr_arg _ (tides p' hr (g i) p hY hi))
end YM.ConnectedActivityE6.Blaze.Vine
