import YM.Further.GAUSSIAN_SCALAR_LEDGER.Hitting
import YM.Next.UV_STRESS.Currency
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Motif
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Reprise
import YM.Push.STRESS_FLUX.Pass

/-!
# E factor costs at fixed broad-principal Z (large/winding and combined)

Requires nonhole authenticated Bulletin and Museum talks on this
component and compatible linear Booths, with NO invoice on the actual
location/motion of the mean. Does not independently chart or re-limit
any partner factor that would use the same U,V in a nonlinear expansion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {g : outfit G f c} {X : Support f} {Y : Support c} {Q M C t r x z δ N ε τ : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {D : Slab G c l} {o : Site f} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}

def grandFee (Q' : Rights G n) := patterns n * Q'.fee

section pleas
variable (Q' : Rights G n) [Fintype I] (a : Museum F x A X Y I) (b : Folio.Bulletin x Pt T) (hT : Act T F x k n r Q)
    (h' : Matins T F B.power (2*C) M) (he : Seed B o X f') (hE : B.supBounds o X f' τ)
    (hQ : 1≤Q) (hC : 1≤C) (hM : 1≤M) (hn : 2≤n) (hl : l ≤ n) (hB : n ≤ B.order) (ht : P.threshold=temp x) (ht' : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (hs : loom P (reach x) C ≤ 1) (hr : loom P (reach x) C < r) (hd : ∀ j, P.dirBound (S.ratio.parent o) (D j)) (U : Config G f) (w : Prices G I) (hu : 0 ≤ u)
include b hT h' he hE hQ hC hM hn hl hB ht ht' hpow hs hr hd hu

-- no Short prerequisite
lemma grand (h : Panes S V x X P n C g) (hw : u*‖tape w‖ ≤ loom P (reach x) C) (hW : Healthy B.threshold X (a.received k T q d u V U w)) :
    let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ grandFee Q' * (ample n X P B Q M C x)^n * τ := by
  intro f₀
  let z := a.overture T k V g w u D; let f := f' ∘ increment (a.received k T q d u V U w)
  have hw (g) := (a.extra_size g u hu w).trans hw
  obtain ⟨hz,hz'⟩ := a.reprise hT h h' he.site hQ hC hM hn hl ht ht' hpow hs hr.le hw hd
  have h0 : z 0=0 := by unfold z Museum.overture; rw [Sample.journey_origin,a.overt_home]
  have hf : ContDiffAt ℝ n f (z 0) := h0.symm ▸ (he.good.smooth _ hW).of_le (Nat.cast_le.mpr hB)
  have HH := a.overt_at (q:=q) (d:=d) hT b h U hC hr hw (W:=fun _ => w) (flowJourney V D) ?ready
  case ready =>
    intro i hi
    let L y := a.pane V u w (g i) i (journey V l D y) w
    have hL : ContDiffAt ℝ n L 0 := (((h.fits i hi).ready D).prodMk contDiffAt_const).prodMk contDiffAt_const
    have he : L 0=a.pane V u w (g i) i V w := by unfold L; rw [Sample.journey_origin]
    exact he ▸ hL.continuousAt.tendsto
  have heq : f₀ ∘ journey V l D =ᶠ[𝓝 0] f ∘ z := HH.mono fun _ hv => he.good.sites _ _ hv
  refine ⟨(hf.comp _ hz).congr_of_eventuallyEq heq,fun j hj => ?_⟩
  rw [(heq.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds]; let A := ample n X P B Q M C x; have hA : 1 ≤ A := ample_one n X P B hQ hM hC
  have ht := hE.1; have hQ := Q'.large
  rw [grandFee,show ample n X P B Q M C x=A from rfl,show (patterns n*Q'.fee)*A^n*τ=patterns n*(A^n*Q'.fee*τ) by ring]
  refine slots_bound hz hf hj (by positivity : 0≤A^n*Q'.fee*τ) (fun p v hv => ?_); rw [h0]
  refine (Q'.born _ _ (fun _ => A) (p.length_le.trans hj) ((p.length_le.trans hj).trans hB) he.good hE hW
    (fun i => hz' _ (p.partSize_pos i) ((p.partSize_le i).trans hj) _ (fun _ => hv _))).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; gcongr; exact p.length_le.trans hj

-- stage finance comes next, not conditional on evaluation point
omit hs hr hn hC ht' in
lemma recital_fee (s : Seam T δ N) (hδ : 0<δ) (h₀ : 0≤N) (hG : G.Simple) (hL : licensed δ N S.patch.L)
    (Web : Web G) (Z : Collar G n) (hc : C=Cube.fee Z) (h : Tension Web δ Q ε x r (loom P (reach x) C) B.threshold)
    (hz : Cube.Wire P (reach x) Z) (hr : Weft G S.patch.L P B Q C x) (hn : 5≤n) (hF : 100*(1+radiusB x)≤c.val) (hV : Healthy P.threshold Y V)
    (hw : u*‖tape w‖ ≤ ε*B.threshold) :
    let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    let y := tranche S.patch.L n Q (loom P (reach x) C) (u*‖tape w‖) B.threshold
    let price := if (coverNumber B.B X)^3 < S.patch.L.val then shortFee Q' * (M+y)^n * ((S.patch.L.val:ℝ)⁻¹)^5 else grandFee Q' * (ample n X P B Q M C x)^n
    ContDiffAt ℝ n (fun z : Directions G c × Prices G I => f' (a.received k T q d u (increment V z.1) U z.2)) (0,w) ∧
      ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ price * τ := by
  subst C; intro f₀ y price; obtain ⟨g,hp⟩ := framed a hV hF (by omega) hz; have hc := Cube.fee_one Z
  have hW := border_healthy s hδ h₀ hL hT hQ (by omega) h a b Z rfl hz hF ht hV U w hu hw B.threshold_pos (q:=q) (d:=d)
  have hw' := hw.trans h.noise; have hY := h.small.trans (min_le_right ..)
  refine ⟨a.joint_receives hT b hp U hc h.allows (fun g => (a.extra_size g u hu w).trans hw') he.good hB hW,?_⟩
  unfold price; split
  · next hS =>
    obtain ⟨g,hg⟩ := a.canvas o (Finset.mem_union_left _ he.site) hV hF Z (by omega) hz
    exact motif Q' hG a b hr hT hg hc h' hQ hM hn hB hF ht h.coarse hpow h.allows hY hS he hE hd hl U w hW hu hw'
  exact grand Q' a b hT h' he hE hQ hc hM (by omega) hl hB ht h.coarse hpow
    ((le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hw') hQ).trans hY) h.allows hd U w hu hp hw' hW
end pleas
end YM.PhysicalNext.JointLoad.Heir
