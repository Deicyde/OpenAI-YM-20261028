import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Rail
import YM.TraceExtension.Prom.Port.CoreBudget
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Rail for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle WeightedGaussianMarginal45C.Issue.Cut UVNext.PricedKernels
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x β g d : ℝ} {A : Stores S} {F : Forest S.ratio}

section era

-- One natural ambient choice: use all active links, zero-pad away.

variable {o : Site c} {W w : ℕ} (k : S.Choices) (q : Chi) (T : Tube G S) {U : ℝ} {V : Config G c} {v : Dir G c}
variable {Pt : Teller G}

end era

-- Four-bond product and support checks separate from getting the μ by an Atlas application.
private lemma checkingMaskSky (P : Finset (Bond f)) (E : Config G f) (u : Cell f) (hR : bones u⊆P)
    (V : Patch) (U : Teller G) {w : ℕ} (he : Enlightened V U w x β) (l z : Dir G f) (g t e : ℝ) (ht : 0<t)
    (hhT : t=phase (betaF G x V.L)) (hD : e=edgeFire G x)
    (hr : ∀ i∈P, ‖g • collect G z i‖ ≤ coolFraction*t ∧ G.chord (E i) ≤ highPrice G*linkRoom x ∧
      ‖G.curvature (E i)-collect G (l+g • z) i‖ ≤ e) (h : ‖Work.F03.faceCurl u l‖ ≤ t/2048) :
    G.chord (faceValue E u) ≤ t/8 := by
    subst e; subst t
    let t:=phase (betaF G x V.L); let e:=edgeFire G x; let a:=coolFraction
    let A' := l + g • z
    obtain b:= hr _ (hR (first_bone _)); obtain c:=hr _ (hR (second_bone _))
    obtain u':=hr _ (hR (third_bone _)); obtain d':=hr _ (hR (last_bone _))
    obtain ⟨_,_,hu⟩ := (Work.E05.curvature_lower G).choose_spec.choose_spec
    let ξ:=faceValue E u; let P0:= Work.F03.faceCurl u A'
    have hs : G.chord ξ ≤ lampRadius G := by
      unfold ξ; rw [corners]; apply le_trans _ he.low
      exact (G.chord_triangle ..).trans ((add_le_add ((G.chord_triangle ..).trans (add_le_add ((G.chord_triangle ..).trans
        (add_le_add b.2.1 c.2.1)) ((G.chord_inv _).trans_le u'.2.1))) ((G.chord_inv _).trans_le d'.2.1)).trans_eq (by ring))
    have hj : ‖g • Work.F03.faceCurl u z‖ ≤ 4*(a*t) := by
      rw [show g • Work.F03.faceCurl u z = Work.F03.faceCurl u (g • z) by
        rw [curl_formula,curl_formula]; simp only [collect, Pi.smul_apply,smul_sub,smul_add]]
      exact curl_price _ u (fun i hi=> (hr i (hR hi)).1)
    have hZ : ‖P0‖ ≤ t/2048+ 4*(a*t) := by
      unfold P0 A'; rw [joined_curl]; exact (norm_add_le ..).trans (add_le_add h hj)
    have hξ := (hu ξ hs).2
    have hX : ‖G.curvature ξ - P0‖ ≤ t/64 := by
      unfold P0; rw [curl_formula]; unfold ξ; rw [corners]
      have hL:=warp4 b.2.1 c.2.1 u'.2.1 d'.2.1
      let P' := fun i=>G.curvature (E i); let R:= P' - collect G A'
      -- precise vector error then mean
      apply (norm_sub_le_norm_sub_add_norm_sub _ (rho P' u) _).trans
      apply le_trans (add_le_add hL (show ‖rho P' u - _‖ ≤ 4*e from ?_)) he.heat
      have h0 : ‖rho P' u - rho (collect G A') u‖ = ‖rho R u‖ := congr_arg norm (by unfold R rho; dsimp only [Pi.sub_apply]; abel)
      change ‖rho P' u - rho (collect G A') u‖ ≤ _
      rw [h0]
      apply (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans
        (add_le_add b.2.2 c.2.2)) u'.2.2)) d'.2.2).trans_eq (by unfold e; ring))
    have hh := (norm_le_norm_sub_add (G.curvature ξ) P0).trans (add_le_add hX hZ)
    have hx : ‖G.curvature ξ‖≤ t/32 := hh.trans (by unfold a coolFraction; linarith only [ht])
    change G.chord ξ ≤ t/8
    nlinarith only [hξ,pow_le_pow_left₀ (norm_nonneg _) hx 2,ht,G.chord_nonneg ξ]

section model
variable {C : Family G} (B : Binding C) {N i p : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "T" => tunnel B N i p
local notation "Θ" => tell B i
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => betaF G (C.path.levels.clock.hatBeta i) (C.S.block i)

local notation "J" => C.path.levels.clock.J i

variable (M : C.Makes) (hi : i<N)
variable {w W : ℕ} {A : Stores (C.path.levels.clock.op i p)} {β β' U d : ℝ}
    {V : Config G (C.side i p)}

include M hi
/-- Main nonlinear observable bound on actual Rank stencil (subsequently use
at paths and for copies). Given the large-enough Pose & payments on both x's, on
every indicated mask:
1. The PHOTO U in these shared variables is itself valid on the fine field patch,
even testing every flag at the boundary; not claimed this covers Frozen throughout the volume.
2. Rank's arguments on f (input of W) that gauges to U, even in this *same held
sample*, are close to the critical bias on the actual coarse V plus the
fluctuation curl (using `Coupling` and `dKeys` precisely).
The errors hold simultaneous where tested, not on unguarded Y.
No translating color indices or identifying expectations across outside configurations. -/
lemma laminateSky (h : Steady G (C.S.block i) (max (B.prices.Ω (C.path.levels.clock.J (i+1))) (B.prices.Ω J)) x (min (B.prices.α (C.path.levels.clock.J (i+1))) (B.prices.α J)) β β') (he : Enlightened (C.path.levels.clock.op i p).patch Θ w x β) (hf : StrongScope (C.path.levels.clock.op i p).patch Θ U x) (o W) (v : Dir G (C.side i p)) (hP : Pose A o W x V v) (k : (C.path.levels.clock.op i p).Choices) (q : Chi)
    (F : Forest (C.path.levels.clock.op i p).ratio) (Y : RoomView A (retime x) F G) (r : Site (C.side (i+1) p))
    (hU : 2*(w*walls y+1)<(C.side (i+1) p).val) (hv : Guards (parasol r (w*walls y)) Y.2 (haze G x β (C.S.block i)))
    (hY : ∀ e∈parasol r (w*walls y), separation o ((C.path.levels.clock.op i p).ratio.parent e.1)+walls x+2 ≤ W) (hc : 100*(1+radiusB (retime x)) ≤ (C.side i p).val) :
    let V' := spine V o
    let L:= w*walls y; let Q:= Spindle.patch L r; let Z:= Y.2
    let U:= gazed T k q V' (retime x) β d Y
    let g:=coupling β
    Healthy (phase y) Q U ∧ ∀ f (t : Site (C.side (i+1) p) → G.El), Lattice.gauge t f = U →
      ∀ j : Incidence G (C.side (i+1) p), separation r j.1 + 2 ≤ L →
        |rigid (coloring (t r) (Tapes.kiosk g r f)) j- ((purseMean B (i:=i) o V (coupling β') (N:=N) j).re + (dKeys A F (retime x) *ᵥ Z) (toPAC j))| ≤ x^(-(1/32):ℝ) := by
  intro V' L Q Z E g
  have hV := ships B N i p M hi
  have hS:= B.sized i p; let l:=low T F v; let z:= breadth Z
  let K := linkRoom x; let f:= highPrice G*K; let e:=edgeFire G x; let t:=phase y; let a:=coolFraction; have ha : 0<a:=coolFraction_pos
  have ht : 0<t:=alpha_phase _ (add_pos_of_pos_of_nonneg h.visible (Work.E04.shift_nonneg G (C.S.block i)))
  have hg : 0<g := coupling_pos h.sparks
  have hM := hf.sight St T rfl hV hS hc (B.world.H N (i+1)) (B.world.H N i)
    (B.prices.η (C.path.levels.clock.J (i+1))) _ _ _ (B.prices.eta_pos _) (B.prices.eta_pos J)
    (B.pays.all N (i+1) hi _) (B.pays.all N i hi.le _) (B.paths N (i+1) hi p)
    (B.sworn N (i+1) hi p) (B.pays.crossings N i p hi) (knot B N i p M hi) _ A o V v hP F k q d .endpoint Y.1
  have hr j (h : j∈parasol r L) := slide_link k q T hP F Y hV he hM.1 j (le_trans (Nat.le_add_right _ _) (hY j h)) h hv
  have hp (u : Cell (C.side (i+1) p)) (hR : bones u ⊆ parasol r L) : G.chord (faceValue E u) ≤ t/8 := by
    have hr' := (pointingSky B hi hP h F u (hY (u.1,u.2.val.1) (hR (first_bone u)))).1
    exact checkingMaskSky (parasol r L) E u hR (C.path.levels.clock.op i p).patch Θ he l z g t e ht rfl rfl (fun i hi=>hr i hi) hr'
  refine ⟨?_,fun Y' f' hY' j hj => ?_⟩
  · apply Finset.disjoint_left.mpr
    intro u h0 hs; obtain ⟨i,hi,he⟩:= (flags_spec ..).mp hs
    have h := hp i (shade_heel.flags _ ⟨u,h0,hi⟩)
    change t < _ at he; linarith only [he,h,ht]
  have hu : (j.1,j.2.1.val.1)∈Room r L := (therm L r (fromBead G j) hj).1
  have hy := (pointingSky B hi hP h F (fromBead G j) (hY (j.1,j.2.1.val.1) (Room_advances (Nat.le_add_right L 8) hu))).2 j.2.2
  exact throughout E L r Z l (C.path.levels.clock.op i p).patch Θ he rfl (purseMean B (i:=i) (N:=N) o V (coupling β')) hU (fun i hi=>(hr i (Room_advances (Nat.le_add_right L 8) hi)).2) j hj f' Y' hY' hy
end model
end YM.PhysicalNext.InteractingRank
