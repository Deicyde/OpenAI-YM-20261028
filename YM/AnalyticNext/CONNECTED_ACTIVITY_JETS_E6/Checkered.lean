import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cincture
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Olive
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tablet

/-!
# Output messages for extended b row, η tiny

Includes torch marking inside orientations even under preserved flag masks.
Absolute Both without asking for correlations/telescope unrelated rows.
Structural support proofs follow.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush  Frond Gate Scroll Vine Tablet
variable {v z r Q s y η γ : ℝ} {j : ℕ} {U : E → Config G c} {x : E}

lemma beam_vec {ι κ : Type} [Fintype ι] [Fintype κ] {a : ι → Site c} {b : κ→ Site c}
    {A : E → Matrix ι κ ℝ} (hp : Tablet j η s v A a b x) {u : E → κ→ℝ} (hr : 0≤r) (hz : 0≤z)
    (hu : ∀ i:κ, Brush j r z (fun x=>u x i) x) (i : ι) : Brush j (s*r) (v+z) (fun x=> (A x *ᵥ u x) i) x := by
  obtain ⟨B,hB,hp'⟩:=hp.shape; unfold Matrix.mulVec dotProduct
  refine (Brush.spree _ _ _ (add_nonneg hp.pos hz) (fun z (_:z∈univ)=> (hB i z).paints (hu z))).climb ?_ le_rfl
  rw [← Finset.sum_mul]; apply mul_le_mul_of_nonneg_right _ hr
  apply le_trans _ (Control.pure_pay hp'.1 hp.scale i)
  exact Finset.sum_le_sum fun j _=> le_abs_self _

namespace Vine

lemma luster (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi)
    (j : ℕ) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (hv : ∀ᶠ x in atTop,0≤V x) :
    ∃ X : ℝ→ℝ, Rate G L (-(1/2)) X ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→ ShellAccess S G x W K γ →
    ∀ (F : Forest S.ratio) (Y : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G c) (z : E), Y.x=x → Y.width=K → Y.χ=χ → Mode U z j (V x) →
      let p i:= vary Y (U i); (p z).manifest → ∀ i, Brush j (|X x|) 1 (fun z=> stand (bar (p z) 0) i) z := by
  obtain ⟨A,hA,hX⟩:= signals G L W γ K j χ h
  obtain ⟨C,hC,hq⟩:= bounded_stencils P D hD
  obtain ⟨e,he,hD⟩:= certifiedBranch P L D hD j h hv
  let m:= royalty G
  let f x:=m*(|A x| *m); let b x:= C*(m*(f x*m)); let d x:= 4*(radiusB x:ℝ)*(V x*royalty G)
  let H x:= b x*(1+(d x+(V x+1+V x)+d x))^j
  refine ⟨fun x=> ‖Coat.scale‖*(e x+H x),?_,?_⟩
  · have hf : Rate G L (-(1/2)) f := ((hA.compare (v:=fun x=> |A x|) (Eventually.of_forall fun i=> (abs_abs _).le)).mul_right _).mul_left _
    have hs := Rate.const (G:=G) (L:=L) (1:ℝ)
    have hz : Rate G L 0 V := h.weaken (by norm_num)
    have hj : Rate G L 0 d := by convert ((Rate.radius_price.mul_left 4).mul (hz.mul_right _)) using 1; ring
    have hc : Rate G L (-(1/2)) H := by
      simpa only [add_zero,zero_mul] using! ((((hf.mul_right _).mul_left _).mul_left C).mul ((hs.add ((hj.add ((hz.add hs).add hz)).add hj)).pow j))
    exact (he.add hc).mul_left _
  filter_upwards [hD,hX, room G P L] with x hX he hp c f S T hS hh ha F Y E _ _ U z hv hw ht hhV p hF i
  subst x
  let y := Y.x
  let X:=p z; let s:= i.fst.fst; let k:= i.fst.snd
  have hj (i:Bond f) := he c f S T hh.length_eq ha E F Y U z ht rfl hw hhV i
  have hx := hp _ _ S T hh
  by_cases hg : Y.selected s (spot S k)
  swap
  · have he z: stand (bar (p z) 0) i=0 := by unfold stand bar; rw [if_neg (show ¬(p z).selected i.1.1 (spot S i.1.2) from hg)]; rfl
    simp_rw [he]; exact (Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl
  let G' (t:E) := strain (p t) s k 0
  have hG : Brush j (e y+H y) 1 G' z := by
    have hk := Blaze.turn hhV s
    apply (hX _ _ S T hS hh (choice s Y.k) k E (fun t=> pull s 0 (U t)) z hk (safe_hull X hF s k hg)).gathering
    rw [show (fun i=> orientedRow T (p i).R s k (p i).V ((p i).signal 0)) =
      (fun i=> straightened T Y.R (pull s 0 (U i)) (displacement s ((p i).saved) (replica S.ratio (U i))) k) from by
        funext i; simp only [Coat.signal, (p i).lens_zero, add_zero]; rfl]
    have ht i := displacement_pay (S:=S) (V:=fun i=> (p i).saved) s i _ _ hhV (hj (edge s i))
    have hn := royalty_ge G; have hm := hhV.pos
    exact ((hard_turn k hx (e:=royalty G *(|A Y.x| *royalty G)) (by positivity) (by exact (ht (0,0)).pos)
      (fun i _=> ht i) hk (hq c f S T hS hh.funds) hC.le).trim)
  have hh (z) : bar (p z) 0 i.1= Coat.scale • G' z := if_pos hg
  unfold stand; simp_rw [hh]; exact (colorEvaluated _ (hG.smul Coat.scale)).climb (le_abs_self _) le_rfl
end Vine
end YM.ConnectedActivityE6.Blaze
