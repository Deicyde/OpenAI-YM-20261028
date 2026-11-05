import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Via

/-!
# Remote affine paths are actually small at local stationary mean, I

Station answer using ONE common V hull around the stencil of all columns
and rows to be read. Keep k fixed in the estimates. Pull Quote/V and Δ
only at orientation tables. No probabilistic step. Future mean locality
proof for V off flags is separate from this patch (price doesn't mean no
dependence lookup). Full zero at outSat. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- Candidate λ lives at all nontrunk in the *same* gauge, though only
using it on the interior patch. Not a sector variable. -/
def radiate (_X : Coat T F) (g : Site c → G.El) (b : LogField G c) : Directions G f := spinRow S g⁻¹ (spring T F b)

lemma upright (X : Coat T F) (g : Site c→G.El) (b : LogField G c) :
    spinRow S g (X.radiate g b)=spring T F b := by
  funext i; unfold radiate spinRow; rw [← G.adjoint_mul, Pi.inv_apply, mul_inv_cancel,G.adjoint_one]
lemma trench (X : Coat T F) (g : Site c → G.El) (b : LogField G c) (i : Bond f) (h : i∈F.trunks) :
    X.radiate g b i=0 := by unfold radiate spinRow; rw [spring_ticks, dif_pos h,map_zero]

lemma breathing (x z : Site c) (V W : Config G c) {B d : ℕ} (s : Signed)
    (h : AgreeNear id x B V W) (he : separation x (s.act z)+(d+1) ≤ B) : AgreeNear id z d (pull s 0 V) (pull s 0 W) := by
  intro i hi
  have ht : separation x (edge s i).1 ≤ B := (separation_triangle x (s.act z) _).trans ((Nat.add_le_add_left
    ((projected_wealth s i z).trans (Nat.add_le_add_right hi _)) _).trans he)
  rw [charge,charge,h (edge s i) ht]

lemma stillbase (X : Coat T F) (x : Mention c f) (s : Site c → G.El) :
    pull x.1 0 (gauge s X.V)= gauge (s ∘ x.1.act) (pull x.1 0 X.V) := by rw [Work.F05.pull_gauge_zero]; simp only [affine0]; rfl
lemma raft (X : Coat T F) (h : Room P S T X.x) (v : Directions G f) (x : Mention c f) (z : Site c→G.El)
    (ho : ¬Inside (root S x) X.seeds (20*X.B)) (hv : ∀ i∈ F.trunks, v i=0) :
    G.adjoint (z (root S x)) (X.realPath x.1 x.2 v) = request T X.x (Oriented.choice x.1 X.k)
      (pull x.1 0 (gauge z X.V)) x.2 + orientedRow T X.R x.1 x.2 (gauge z X.V) (spinRow S z v) := by
  have hy : orientedRow T X.R x.1 x.2 X.V (X.signal v)=orientedRow T X.R x.1 x.2 X.V v := by
    apply raw_near T h _ _ _ _ _ _ (fun _ _ => rfl); intro i hi
    by_cases hh : i∈F.trunks
    · rw [X.on_trunk v i hh,hv _ hh]
    have he : distAt S i (root S x) ≤ X.B/4 := hi
    have hq : 0 < X.B := lt_of_lt_of_le (by norm_num) h.sight.1
    exact X.at_hot v i (far_active X.seeds F i (clear ho (u:=10*X.B+1) (by unfold distAt at he; omega)) hh)
  obtain ⟨_,_,hP,-⟩ := h.accepted.feeds
  rw [oriented_under T hP,realPath,hy,map_add]; congr 1
  rw [request,request,map_sub, stillbase X]
  rw [reference_v _ h.accepted,guide_gauge h.accepted]; rfl

/-- Annular excess priced in H200; here price REAL far square after
projection using smaller hull. Use A,R frame not volume-norm stationary
solve. This is uniform through all α in that frame. Coarse V among all,
with output flags correct. -/
lemma retreat (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G)
    {w : ℝ → ℝ} (hw : Rate G L (-(1/2)) w) (hh : ∀ᶠ x in atTop,0≤w x) :
    ∃ E : ℝ → ℝ, Rate G L (-1) E ∧ ∀ᶠ x in atTop, 0 ≤ E x ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → S.patch.L=L → Room P S T x →
    Stamp T → ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → X.manifest →
      ∀ (p : Mention c f) (z : Site c → G.El) (b : LogField G c),
      let o := root S p
      ¬Inside o X.seeds (20*X.B) →
      AgreeNear id o (2*X.B) (gauge z X.V) (represent b) → ‖b‖ ≤ w x →
        ‖X.realPath p.1 p.2 (X.radiate z b)‖ ≤ E x := by
  obtain ⟨Z,hZ,h⟩ := read_guides P L hw hh
  obtain ⟨M,Y,hM,hY,H⟩ := SliceRows.within P L D hd hw hh
  obtain ⟨C,hC,hx⟩ := spring_cap P
  obtain ⟨B,hB,hb⟩ := bounded_stencils P D hd
  obtain ⟨A,r,hA,hr,H₂⟩ := chord_chart_cost G
  let U x := B*(2*G.colorScale*((radiusB x:ℝ)+1)*(A*w x)*(C*w x))
  let K x := B*(C*w x)*Real.exp (-P.top.width*till x)
  have hU : Rate G L (-1) U := by
    convert (((((((Rate.radius_price.add (Rate.const 1)).mul_left (2*G.colorScale)).mul (hw.mul_left A)).mul (hw.mul_left C)).mul_left B))) using 1; norm_num
  have hK : Rate G L (-1) K := by
    convert (((hw.mul_left C).mul_left B).mul (Rate.cutoff (a:=-(1/2:ℝ)) P.top.width_pos)) using 1; norm_num
  refine ⟨_, ((hY.add hZ).add hU).add hK,?_⟩
  filter_upwards [h,H,hw.below (by norm_num) _ hr,hh] with x hy hs hW hh
  have hk := hB
  have hg : 0 ≤ U x := by unfold U; have:=G.colorScale_pos; positivity
  have hE : 0 ≤ K x := by unfold K; positivity
  refine ⟨(by have := hs.2.1; have := hy.1; linarith),?_⟩
  intro c f S T hS hL hR h F X hX hV p z b o hN he hw
  subst x
  let s := p.1; let i:=p.2; let F₀:=focus S i
  let d := X.B; let t:=Oriented.choice s X.k
  let v := spring T F b
  let V := pull s 0 (gauge z X.V); let b' := pulled b s
  have hx : ‖v‖ ≤ C*w X.x := (hx S T hR.accepted F _).trans (mul_le_mul_of_nonneg_left hw hC.le)
  have hv' : ‖b'‖ ≤ w X.x := (light_pull ..).trans hw
  have h0 : 100 ≤ d := hR.sight.1
  have hv : AgreeNear id F₀ (d/4) V (represent b') := by
    rw [show represent b'=pull s 0 (represent b) from Eq.symm (by simpa only [one_smul] using represent_pulled s b (1:ℝ))]
    apply breathing o _ _ _ s he
    have h : separation o (s.act F₀)=0 := separation_self _; unfold d at *; omega
  have hClean : Clean V X.x F₀ (d/4) := by
    have hh := clean_far X.seeds (gauge z X.V) (o:=o) (by rw [RG.gauge_flags]; exact hV) hN
    apply Clean.turn
    exact hh.shrink (by change separation o o+d/4 ≤ 20*d; rw [separation_self]; omega)
  have ht := hy.2 c f S T hL hR V b' hv'
  have hu := ht.1 i hClean hv
  have uf := hs.2.2 c f S T hS hR b' V (replica S.ratio V) 0 t i hv' hv (show Grafted V (replica S.ratio V)
    (0 : Directions G f) F₀ (d/4) (w X.x) S from ⟨fun j _ => by simp [increment],fun _ _ => by simpa only [Pi.zero_apply,norm_zero]⟩)
  dsimp only at uf hu
  let D' := barField T X.R (displacement s v 1) i
  let C' := uncutField T (displacement s v 1) i
  have hp : Bounded T P.top.width B := hb c f S T hS hR.accepted
  have hU' : ‖orientedRow T X.R s i (gauge z X.V) v-D'‖ ≤ U X.x := by
    have hc : ∀ j : Bond c, separation o j.1 ≤ d+1 → G.chord (gauge z X.V j) ≤ A*w X.x := by
      intro j hj; rw [he j (show separation o j.1 ≤ 2*d by omega),Work.F03.represent_link]
      have hb := (norm_le_pi_norm b (pole j)).trans hw
      exact (H₂ _ ((hb.trans (le_abs_self _)).trans hW)).trans (mul_le_mul_of_nonneg_left hb hA.le)
    have hB := hR.sight.2
    have hi := spinning hR.accepted hk hp (gauge z X.V) X.R d s i (show 0≤C*w X.x by positivity)
      v (fun j _ => (norm_le_pi_norm _ _).trans hx) (by unfold Coat.R d Coat.B; omega) (show 0≤A*w X.x by positivity) hc
    rw [show orientedRow T X.R s i 1 v=D' from by unfold orientedRow; rw [replica_one,show pull s 0 (1 : Config G c)=1 from by funext i; rw [Channel.charge]; simp, flat_strip]] at hi
    exact hi
  have ht' := (hp.tail (displacement s v 1) X.R i).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((displacement_bounded ..).trans hx) hk.le) (Real.exp_pos _).le)
  have heq := rear hR.accepted h F b s i
  rw [← G.norm_adjoint (z o), X.raft hR _ p z hN (X.trench z b), X.upright]
  let x := linearCost T (toLog (linearCopy S.ratio (collect G b'))) b' i
  let D := orientedRow T X.R s i (gauge z X.V) v
  change ‖request T X.x t V i+D‖ ≤ _
  rw [show request T X.x t V i+D= (baseStroke T X.x t V i-x)-(guide T X.x V i-linearGuide T b' i) + (D-D')+(D'-C') from by
    change (x-linearGuide T b' i)+C'=0 at heq; unfold request; rw [← sub_zero (baseStroke T X.x t V i-guide T X.x V i+D),← heq]; abel]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add uf.2.2 hu)) hU')) ((norm_sub_rev D' C').trans_le ht'))
end YM.ConnectedActivityE6.Coat
