import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cues
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cylinder
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flash
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Ports

/-!
# A reusable same-step law on a Hill of all readable local marginals

Old: actual endpoints (or Mid geometry choice inside Sector), in
SMALL V patch gauge, covariance of active chart variable, centered with
`meanLog` (or correspondingly ordered midpoint source). Alternative:
ideal uncut inverse in full Active tree register (with all the missing
frozen positions), centered at firstTerm solve for actual v. Both with
the *same* fine beta coupling before inverse/exponent, from calling
Teller/V₀ (integrable even on Haar, licensing demanded separately).
`K`, read-card powers post-L then absorbed via anisotropic availability
(Tiny small powers here sufficient). Gives exact correction **before**
comparing bounded probe moments, retains scalar and exponential even
in that use if desired. No density factor between a curved and ideal
on *full* stencil beyond the no-hole theorem; instead read measures,
include only their compatible corners. This gives $x^{-1/16}$ over
any size & placements reaching as stated across delayed x; no constraint
on positions or growth of the rest of the torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Local
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Density
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x β : ℝ}

lemma stress {v n m : Type} [Fintype n] [Fintype m] [Fintype v] [DecidableEq n] [DecidableEq m] [DecidableEq v]
    (Q : Gaussian.Table n) (K : Gaussian.Table v) (m0 : n→ℝ) (m1 : v→ℝ) (g : ℝ) (hg : g≠0) (e : m↪n) (d : m↪v)
    {x h A : ℝ} (hQ : Q.PosDef) (hK : K.PosDef) (hh : 0≤h) (ha : 1≤A) (hx : A*h≤1/2)
    (h_cov : ∀ z : m, |g⁻¹*(m1 (d z)-m0 (e z))| ≤ h) {c : Side} (p : m→Site c)
    (hM : let C:=Q.submatrix e e; let B:=K.submatrix d d
      let u := (native c).Schur p p 0 A
      u C ∧ u C⁻¹ ∧ u B ∧ u B⁻¹ ∧ (native c).Schur p p 0 h (C-B))
    (H : let N : ℝ:=Fintype.card m; h*(2*A*N*(1+1^2)+2*(A^2+A)*(N*A))≤x^(-(1/16):ℝ)) :
    let C:=Q.submatrix e e; let B:=K.submatrix d d; let w:=g⁻¹ • (m1 ∘ d-m0 ∘ e)
    let N : ℝ:=Fintype.card m
    (∀ y, |Real.log (Density.replace C B w y)| ≤ h*(A*N*(1+1^2)+(A^2+A)*Density.energy y)) ∧
    ∀ F : (m→ℝ)→ℝ, Measurable F → ∀ W : ℝ, (∀ y, |F y|≤W) →
      let X:=∫ z,F ((m0+g • z) ∘ e)∂cloud Q
      X = (∫ z,Density.replace C B w z*F ((m1 ∘ d)+g • z)∂cloud B) ∧
      |X-∫ z,F ((m1+g • z)∘ d)∂cloud K| ≤ W*x^(-(1/16):ℝ) := by
  intro C B w N
  obtain ⟨hC,hA,hB,hW,hr⟩:=hM
  have hv:=Density.countHeal (D:=native c) (p:=p) (A:=C) (B:=B) le_rfl hh ha hx (hQ.submatrix e.injective) (hK.submatrix d.injective) hC hA hB hW hr w (t:=1) fun i=>by rw [mul_one]; exact h_cov i
  refine ⟨hv.1,fun F hf W hs => ?_⟩
  let M n z := F (n+g • z)
  have hm (x : m→ℝ) : Measurable (M x) := hf.comp (by fun_prop)
  have he := Density.billed e hQ.posSemidef (M (m0 ∘ e)) (hm _)
  have hd := Density.billed d hK.posSemidef (M (m1 ∘ d)) (hm _)
  intro X
  have h1 : X=∫ z,M (m0 ∘ e) z∂cloud C := he
  rw [h1,show (∫ z,F ((m1+g • z)∘ d)∂cloud K)=∫ z,M (m1 ∘ d) z∂cloud B from hd]
  have hg' : (m0 ∘ e)+g • w=m1 ∘ d := by unfold w; rw [smul_smul,mul_inv_cancel₀ hg,one_smul,add_sub_cancel]
  constructor
  · rw [(Density.exchange _ _ (hQ.submatrix e.injective) (hK.submatrix d.injective) w _).2]
    congr 1; ext z; unfold Density.priced M; rw [smul_add,add_left_comm,hg',add_comm,smul_eq_mul]
  have hc := hv.2 0 (M (m0 ∘ e)) W (le_trans (abs_nonneg _) (hs 0)) (hm _) (fun z=>hs _)
  have hI : ∀ z, M (m0 ∘ e) (w+z)=M (m1 ∘ d) z := by intro; unfold M; rw [smul_add, ← add_assoc,hg']
  simp_rw [zero_add,hI] at hc
  exact hc.trans (by rw [mul_comm h W,mul_assoc]; apply mul_le_mul_of_nonneg_left H ((abs_nonneg _).trans (hs 0)))

variable (T : Tube G S) (U : Stores S) (F : Forest S.ratio) (k : S.Choices) (x : ℝ) (V : Config G c) (g : Geometry)
def panoramic := pane (sectorW G S x U F g) (Rows.gram T x V k (shots S x) U F) 0
def portrait (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen U x F)) := offCenter (panoramic T U F k x V g)
  (Rows.blame T x V k (shots S x) U F q d Y)
def palette := mirror (panoramic T U F k x V g)
def portrait_head (v : Dir G c) :=
  tape.symm (fun i : F.Free => Lift.doc T F v i.val)
lemma head_entry (v : Dir G c) (i : In x U F (G:=G)) : portrait_head T F v (loadLink U F x i)=Lift.marked U x F (Lift.doc T F v) i := rfl
variable {T U F k x V g}

def Workshop (x : ℝ) (R : ℝ) {S : StepData c f} (A : Stores S) (T : Tube G S) (H : Bed) (o : Site c) (V : Config G c) : Prop :=
  ∀ (F : Forest S.ratio), ∃ (z : Site c→G.El) (v : Dir G c),
    (AgreeNear id o (radiusB x) (Lattice.gauge z V) (represent v) ∧ ‖v‖ ≤ R*clearanceFare x) ∧
    let J:= treeInverse G S F H.metric 0; let b := portrait_head T F v
    J.PosDef ∧ ∀ (k : S.Choices) (q : Chi) (d : ℝ) (g : Geometry) (Y : LinkArray G (Frozen A x F)),
      let a:=portrait T A F k x (Lattice.gauge z V) g q d Y
      let Q:=palette T A F k x (Lattice.gauge z V) g
      Q.PosDef ∧ ∀ (m : Type) [Fintype m] [DecidableEq m] (e : m ↪ In x A F (G:=G)), lives m F A o (radiusB x/4) e →
        ∀ β : ℝ, 0<β → β ≤ 3*x →
        let g:=coupling β; let N : ℝ:=Fintype.card m; let P:=x^(1/128:ℝ)
        let l:= e.trans (loadLink A F x)
        let D:= Q.submatrix e e; let B:= J.submatrix l l
        let u:=g⁻¹ • (b ∘ l - a ∘ e)
        (∀ z, |Real.log (Density.replace D B u z)| ≤ x^(-(1/8):ℝ)*(P*N*(1+1^2)+(P^2+P)*Density.energy z)) ∧
        ∀ (L : (m→ℝ)→ℝ) (C : ℝ), Measurable L → (∀ y, |L y|≤C) →
          let X:=∫ z,L ((a+g • z)∘e)∂cloud Q
          X = (∫ z,Density.replace D B u z * L (b ∘ l+g • z)∂cloud B) ∧
            |X-(∫ z,L ((b+g • z)∘l)∂cloud J)| ≤ C*x^(-(1/16):ℝ)

set_option maxHeartbeats 400000 in
/-- Simultaneous on any same-step patch/Lo chooses via purchases
below. Tested supply is *after* authentic gauge rotation (recall
Gauged.stays). F may vary freely even from block to block. `x^-(1/16)`
normalization NOT $exp$ loss, works for any β in indicated polynomial
(up to same step). Can merge with both center-correction laws and
moment comparison. Keeps covariance polarity (center measured in
physical link with Lie color metric); integrals don't include constraints
from Γ,Frozen and are only in Z at the actually tested measures (shift
using x-scale law and density, no assertion that unbounded polymer
probes remain bounded). Use Tens simultaneously as well for $PW$ cover.
No beta height assumed in Imported module itself: must delay prior.
-/
theorem hill (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) :
    ∃ R : ℝ, 1≤R ∧ ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    ∀ (H L : Bed) (a m D V : ℝ), 0<a → 0<m → Floor H T.high f a V → Floor L T.low c m D →
      Attached H T.up → Attached L T.down → Sworn H f G → Sworn L c G → Towers.Diagonal S H L T.R → Towers.Roll S H L T.R T.high T.low →
      Larger (G:=G) S → 100*(1+radiusB x)≤c.val →
    ∀ (A : Stores S) (o : Site c), Clears A x o (radiusB x) → ∀ V : Config G c, A.flags=RG.flags (temp x) V →
      Workshop x R A T H o V := by
  obtain ⟨Y,η,K,σ,E,hY,hη,hK,hσ,hE,H⟩ := released G P Pt hp Pt.top.width Pt.top.paths Pt.top.width_pos Pt.top.paths_pos.le
  obtain ⟨p,s,M,C,E',g1,hp',hs,hM,hC,hE',hg1,H'⟩ := LocalGaussianLaws.quote G P Pt hp
  obtain ⟨R,hR,hZ⟩ := mean_shot G P Pt hp
  let q := η/(K+1)^2
  have hq : 0<q := by unfold q; positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [hZ,H',H,limited G P (show 0≤(1:ℝ) from zero_le_one),limited G P (zero_le_one.trans hC),limited G P (show 0≤g1⁻¹ from (inv_pos.mpr hg1).le),
    limited G P (inv_pos.mpr hq).le, limited G P (inv_pos.mpr hη).le,Extra.Iteration.Scales.first E (1/4) hE,powers (1+K) (by positivity)] with x hv hQ hx hA hC0 he1 hκ h₃ he0 hek
  let T0 := room x; let B₀ := x^(-(1/4):ℝ); let U:= x^(-(1/8):ℝ)
  obtain ⟨hx0,hx1,hA',huβ,hg⟩ := hek
  have he : 0<x := by linarith
  have hx2 : 0≤B₀ := by unfold B₀; positivity
  have hT0 : 0≤U := by unfold U; positivity
  intro c f S T hP hh H₁ H₂ u m N M0 hu hm hH hH' hw ht HV HW Hc Hr hS hT A o hV V hb F
  obtain ⟨D,W,hD,hW⟩ := hh.feeds
  rw [← hh.high] at hD
  obtain ⟨z,HZ,HW',h_cov⟩ := hx.2 S T hP hh hS hT D hD A o hV V hb
  let Q:=Lattice.gauge z V
  have hB : A.flags=RG.flags (temp x) Q := by unfold Q; rw [gauge_flags,hb]
  obtain ⟨v,hv',he_mean⟩ := hv S T hP ⟨hh,H₁,H₂,u,M0,m,N,hH,hH',hw,ht,HV,HW,Hc,Hr⟩ hT A o hV Q hB HZ HW' -- uses Q not V
  refine ⟨z,v,hv',?_⟩
  intro J b
  let hX : FreeResolvent.Gap (treeMatrix G S F H₁.metric) (treeFare G S.patch S.kernel u) := tree_gap S F _ hS hu ⟨fun i => (hH.uniform.1 i).1⟩
  let Q0:=treeMatrix G S F H₁.metric
  have hHQ : Q0.PosDef := by
    refine gap_positive (Matrix.IsSymm.submatrix ?_ _) hX (treeFare_pos G S.patch S.kernel hu)
    exact FreeResolvent.full_symmetric _ hH.symmetric.1
  have h_inv : J=Q0⁻¹ := by unfold J treeInverse resolve; rw [zero_smul,add_zero]
  have hj : J.PosDef := h_inv.symm ▸ hHQ.inv
  refine ⟨hj, fun k χ d g y => ?_⟩
  intro a X
  obtain ⟨Hi,Hc'⟩ := hQ.2 S T hP hT hh A F k Q hB
  let XX V:=Rows.gram T x V k (shots S x) A F
  have hL : Closes (native c) (front A F) (XX Q) (sectorW G S x A F g) s M p C (E' * Real.exp (-s*radiusB x)) g1 := by cases g; exact Hi; exact Hc'
  obtain ⟨Ha,HY⟩ := h_cov F g k
  let l:=official A F (x:=x) (G:=G); let V':=bareStores S
  let r:=opened G S x V' F (bare_is_Clear S x F)
  let ν:=panoramic T V' F k x 1 g
  obtain ⟨hk,hF,_⟩ := HY H₁ H₂ T.R u m N M0 T.low hu hm hH hH' hw Hc HV
  have Hflat : (native c).Schur (theta S.ratio F) (theta S.ratio F) σ (K*Real.exp (-E*(radiusB x))) (mirror (ν.submatrix r r)-J) := by erw [h_inv]; exact hF.cov
  have hp' : X.PosDef := hL.cloud
  refine ⟨hp',fun I H1 H2 e₀ hi β hβ hI => ?_⟩
  intro α N0 P0 l' D0 B u
  let ht' := slotCount G S (radiusB x)
  have hC1 (k : ℝ) (h : 0≤k) (HP : slotCount G S (radiusB x/4)*k ≤ T0) : N0*k ≤ T0 :=
    (mul_le_mul_of_nonneg_right (reach o (D:=radiusB x/4) e₀ hi) h).trans HP
  have hc : N0 ≤ T0 := by simpa using hC1 1 zero_le_one (hA S hP)
  let v' := Fintype.card I
  obtain ⟨h_work,Hwork⟩ := hA' N0 (Nat.cast_nonneg _) hc
  refine (let V := stress X J a b α (coupling_pos hβ).ne' e₀ l' hp' hj hT0 hx1 huβ (?_) (front A F ∘ e₀) ?_ Hwork
          And.intro V.1 (fun f C hf hm => V.2 f hf C hm)) -- f P0 etc
  · intro i
    obtain ⟨HX,HK⟩ := he_mean F k χ d y (e₀ i) (hi i) g
    rw [← HX] at HK
    rw [abs_mul,abs_of_nonneg (inv_pos.mpr (coupling_pos hβ)).le,abs_sub_comm]
    apply (mul_le_mul_of_nonneg_left (show |a (e₀ i)-b (l' i)| ≤ x^(-(7/8):ℝ) from HK) (inv_pos.mpr (coupling_pos hβ)).le).trans (hg β hβ hI)
  · have hx (i j : In x A F (G:=G)) := entry (show (native c).Schur (front A F) (front A F) _ _ X from hL.compares.1) hs.le i j
    obtain ⟨-,hQ,hN⟩ := affordable (D:=native c) e₀ hg1 hL.gap_cov (zero_le_one.trans hx1) hp' hx (zero_le_one.trans hC) (front A F ∘ e₀) (hC1 C (zero_le_one.trans hC) (hC0 S hP)) (hC1 g1⁻¹ (inv_pos.mpr hg1).le (he1 S hP))
    have hR0 : FreeResolvent.Gap J q := by rw [h_inv]; exact flipped_gap hη hk hK.le (hF.pays.mono hσ.le le_rfl)
    have he_inv : ∀ i j, |J i j| ≤ η⁻¹ := by rw [h_inv]; exact hk.point hη (Q0.mul_nonsing_inv (hk.unit_det hη))
    obtain ⟨-,hQ0,hN0⟩ := affordable (D:=native c) l' hq hR0 (zero_le_one.trans hx1) hj he_inv (inv_pos.mpr hη).le (front A F ∘ e₀) (hC1 η⁻¹ (inv_pos.mpr hη).le (h₃ S hP)) (hC1 q⁻¹ (inv_pos.mpr hq).le (hκ S hP))
    refine ⟨hQ,hN,hQ0,hN0,cheaply (mul_nonneg (by positivity : 0≤1+K) hx2) ?_ h_work⟩
    intro i j
    let Y' := mirror (ν.submatrix r r)
    let M':=panoramic T A F k x Q g
    let i':=l' i; let j':=l' j
    have hp1 : |X (e₀ i) (e₀ j)-Y' i' j'|≤B₀ := by
      have hi' (x y : I) : |M' (e₀ x) (e₀ y)-ν (r (l' x)) (r (l' y))| ≤ B₀ := Ha _ _ ((hi y).trans (by omega))
      change |(1/2:ℝ)*(M' (e₀ i) (e₀ j)+M' (e₀ j) (e₀ i))-1/2*(ν (r i') (r j')+ν (r j') (r i'))| ≤ _
      have h1 := hi' i j; have h2 := hi' j i; have hh := half_keep h1 h2
      apply Eq.trans_le _ hh; congr 1; unfold i' j'; ring
    have hp2 : |Y' i' j'-J i' j'| ≤ K*B₀ := (entry Hflat hσ.le i' j').trans (mul_le_mul_of_nonneg_left he0 hK.le)
    change |X (e₀ i) (e₀ j)-J i' j'|≤_
    rw [show X (e₀ i) (e₀ j)-J i' j'=X (e₀ i) (e₀ j)-Y' i' j'+(Y' i' j'-J i' j') by ring]
    exact (abs_add_le ..).trans ((add_le_add hp1 hp2).trans_eq (by ring))

end YM.AnalyticBridge.LocalGaussianLaws.Local
