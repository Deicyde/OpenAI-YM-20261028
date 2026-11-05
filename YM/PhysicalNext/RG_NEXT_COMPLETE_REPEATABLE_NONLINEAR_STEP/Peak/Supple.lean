import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
/-!
 # Earned from strip on true payload at Deep*d (pre-S.P.width). Mod n ensures adequate Even.
    Use Newt on A0 alone. Adaptation of Op.row_home,T.R.A.B Includes ψ read different Fight.L.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open MultiNext.SignedSource Newt
open Function Filter Finset Lattice Wilson RG Labels Laurent Bloch Exterior Precision Matrix
open Pattern Next.Free Lyre Banjo Mom
open JointLoad.Heir ProofPorts
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {α : ℝ}(G:Gauge)
theorem homeAL (h : 0 < α) (A : ℝ) (k b : ℕ) : ∃ C : ℝ,1 ≤ C ∧ ∀ (c n : Side) (g : Ratio c n) (T : Towers g.count)
    (_T : ∀ s:List Axis,s.length ≤ k→Row.strip (advanceC g.count T.A0 s) α (A / (g.count.val:ℝ)^(1+s.length))) (P : BudgetPoint) (o : Site n), Odd g.count.val → P.power=b →
    ∀ u : Co c (TypeFace 1) → G.Color,(∀ i, ‖u i‖ ≤ P.threshold*(1+(separation i.1 (g.parent o):ℝ))^b) →
    blown C P g.count.val k o (roll G g T u) := by
  obtain ⟨C,hC,H⟩ := straps (m:= TypeFace 1)
      (m':=TypeFace 1) (E:=G.Color) b h
  let s := (Fintype.card (TypeFace 1) : ℝ)
  let M := C*s*|A|
  refine ⟨max M 1,le_max_right ..,fun c n g T hT P o hO hP u hu i l hl z => ?_⟩
  let v := Exterior.coord i
  have he (s : List Axis) (hs : s.length ≤ k) := hT s hs
  have hW (s : List Axis) (hs : s.length ≤ l.length) : Whole (advanceC g.count T.A0 s) :=
    ⟨α,_,h,he s (hs.trans hl)⟩
  change ‖iterate (fun z => load (installed g T.A0) u (wrap n z+o,v)) l z‖ ≤ _
  let B : ℝ := g.count.val; let x := B⁻¹^(1+l.length)
  let t := (1+B⁻¹*size z)^P.power
  have hx : 0 ≤ x := by unfold x B; positivity
  have ht : 0 ≤ t := by unfold t B; positivity
  let K := A/B^(1+l.length)
  let f := advanceC g.count T.A0 l.reverse
  have hf : Row.strip f α K := by simpa only [List.length_reverse] using he l.reverse (by simpa)
  have hk : 0 ≤ K := by
    obtain ⟨h0,h1,h2⟩ := hf (0,v) v
    exact (tsum_nonneg h0).trans h2
  rw [Newt.spatial g T.A0 u l hO hW]
  change _ ≤ max M 1 * P.threshold*x*t
  apply (H c n g f _ P.threshold u o hf hk P.threshold_pos.le hu z v).trans
  change C*s*K*P.threshold*(1+B⁻¹*size z)^b ≤ _
  rw [←hP,show K=A*x from by unfold K x; rw [div_eq_mul_inv,inv_pow]]
  refine le_trans (b:=M*P.threshold*x*t) ?_ ?_
  · change _*_*t ≤ _; unfold M
    rw [show C*s*(A*x)*P.threshold=C*s*A*P.threshold*x from by ring]
    gcongr <;> first | exact P.threshold_pos.le | exact le_abs_self _
  gcongr <;> first | exact P.threshold_pos.le | exact le_max_left .. 

open Pressure Next RG.Supply Next.SectorChange Tree Bid UVNext.PricedKernels
variable {c f : Side}{S : StepData c f}
-- hooks expressed on T.C.Core for earlier

def glider (T:Tube G S)(d b:ℕ)(M C:ℝ) : Prop:= ∀ (B:BudgetPoint)(X:Support f)(o:Site f)(v:Directions G c), B.power=b → Limb b (S.ratio.parent o) v (M*B.threshold) → Promise d C ((S.patch.L.val:ℝ)⁻¹) B o X (route T v)

lemma cradle (d b : ℕ)(M : ℝ)(A : ℝ)(hM : 0<M)(hb: d≤b) (hp : 0<α) : ∃ C:ℝ,1≤C ∧ ∀ {c f:Side} (S : StepData c f)(T: Pressure.Tube G S),
    (∀ l:List Axis,l.length ≤ d→ (advanceC S.patch.L T.R.A0 l).strip α (A/(S.patch.L.val:ℝ)^(1+l.length)))→ Peak.glider G T d b M C:=by -- G explicit?
  obtain ⟨Q,hq,hQ⟩ := homeAL G hp A d b
  obtain ⟨Y,hy,hY⟩:= Newt.canal G d b hb
  let C := 1+M*Y*Q; have hc : 1 ≤ C:= by unfold C; exact le_add_of_nonneg_right (by positivity)
  refine ⟨C,hc, fun S T H B X o v hB hv=> ?_⟩
  let R:= S.ratio
  have hL : 1 ≤ (S.patch.L.val:ℝ) := Nat.one_le_cast.mpr S.patch.L.property
  let y := M⁻¹ • Flat.labels v
  have hpt i : ‖y i‖ ≤ B.threshold * spine b i.1 (R.parent o) := by
    unfold y; rw [Pi.smul_apply,norm_smul_of_nonneg (inv_pos.mpr hM).le]; exact (inv_mul_le_iff₀ hM).mpr ((hv _).trans_eq (mul_assoc ..))
  obtain ⟨w,hf,hg,hw⟩ := hY _ X o B _ _ _ hB hL (zero_le_one.trans hq)
    (hQ _ _ R _ H B o S.patch.odd_side hB y hpt)
  let N : ℝ := S.patch.L.val
  refine ⟨fun i => M • w i,?_,fun i => ⟨by positivity,fun j => ?_⟩,fun i hi => ?_⟩
  · rw [← Finset.smul_sum,← hf]
    funext i; rw [JointLoad.Heir.route,roll_as,Pi.smul_apply]; change Newt.load _ _ _=M • Newt.load _ y _; unfold Newt.load y; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [smul_comm M,Pi.smul_apply,smul_inv_smul₀ hM.ne']
  · change ‖M • w i j‖ ≤ _; rw [norm_smul_of_nonneg hM.le]; refine (mul_le_mul_of_nonneg_left ((hg i).2 j) hM.le).trans ?_
    have he : M*(Y*Q) ≤ C := by unfold C; nlinarith
    calc
      _ = (M*(Y*Q)*N⁻¹^(i.val+1))*Lyre.width B o j := by unfold N; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (by unfold N; positivity)) (Lyre.width_pos ..).le
  rw [Mom.screen, map_smul]
  exact (Mom.Maps o X (i.val+1)).smul_mem _ (hw i hi)
end YM.PhysicalNext.Repeat.Peak
