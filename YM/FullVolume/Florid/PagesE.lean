import YM.FullVolume.Florid.Strata
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' fq:ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d fq)
open Lyre Charity Blaze.March
variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
variable {V':ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V' k)
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
set_option quotPrecheck false
local notation "τ"=> V.pole.turn.badge S
local notation "Q'" => Empire.stella Q
local notation "Φ"=> jewelDebt V.pole (Empire.stella Q) L x₀
local notation "B₀" => radiusB x₀
local notation "π"=> Lyre.spicesF G (r+fq) L' (V' x₀) K j
-- selected under stellar props. Keep Φ factors integrated outside tree.
local notation "hτ" => lushE M V α ν (π) p (k+j)
open Greenbelt
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U₀:E→ Config G c} {s:E}
lemma stations {p a:ℝ} (x:E) (k:ℕ) (f : ℝ→E→ℝ) (hp:2≤p)(hQ : 0≤a)
    (h :∀ (w:Rung) (v:ℝ), (∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/p)^i)‖ ≤ v)→ Brush k (v*a) 1 (fun x=> FullVolume.Ray.trace w (fun t=>f t x)) x): Weigh k x (p/2) (2*a) 1 f:=by
  have hv (i:↑FullVolume.Ray.sun):ContDiffAt ℝ k (f i.val) x:= by
    let w:Rung:= Finsupp.single i 1
    have he:∀ j:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/p)^j)‖≤1:= fun j=> by
      simp only [FullVolume.Ray.trace,w,Finsupp.support_single_ne_zero _ (by norm_num: (1:ℝ)≠0),sum_singleton, Finsupp.single_eq_same, one_smul, Real.norm_eq_abs]; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ratio_le (by linarith) i.property)
    have hh:= (h w _ he).smooth; change ContDiffAt ℝ _ (f i.val) x; simpa [FullVolume.Ray.trace,w] using hh
  have h₀ :0<p:=by linarith
  refine ⟨zero_le_one,fun i hi=> hv ⟨i,hi⟩,fun u hu j hj=>?_⟩
  have he: Rebar p (fun t=> FullVolume.Ray.marked j (f t) x u) a := by
    refine ⟨by linarith,hQ,fun w v he=> ?_⟩
    have h' := point_norm (h w v he) hj hu
    rw [one_pow,mul_one] at h'
    refine (le_of_eq (congr_arg (‖·‖) ?_)).trans h'; unfold FullVolume.Ray.marked FullVolume.Ray.trace
    have hb (i:↑sun) : ContDiffAt ℝ j (f i.val ∘ FullVolume.Ray.tintM x u) 0:= sheen ((hv i).of_le (Nat.cast_le.mpr hj)) u
    exact ((iteratedDeriv_fun_sum (fun i (hi:i∈w.support)=> (hb i).const_smul (w i))).trans (sum_congr rfl fun i hi=> iteratedDeriv_fun_const_smul (hb i) (w i))).symm
  have hi:= he.recovery (a:=p/2) (by linarith) (half_lt_self h₀); rw [show (1-p/2/p)⁻¹=2 by field_simp; ring] at hi; simpa using hi
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma noPage {i:Molecule S}(Z:Coat T F)(F: Leaf R) (he:¬ Ac.Spark (areas R T Q.halo Z.B) i∨¬troupe T R Q.halo Z.B i):F.picture Z i W o.a Q.table Q.halo=0:=by
   unfold Leaf.picture; apply integral_eq_zero_of_ae; filter_upwards with y; exact if_neg (not_and_or.mpr he)
-- orbit through full Story
variable (hp:foam Q L)(hb:R.p.B≤2*radiusB x₀)(hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))
include hp hb hA hc D M hh hr W' Y'
set_option maxHeartbeats 400000 in
lemma tires (X: Coat T F) (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hy:U₀ s=X.V) (hU:Mode U₀ s j u) (i:H.ThinP) (h:Healthy (Pressure.temp x₀) (H.smallAt i) X.V):
    let f(y:E)(t:sun):=(V.flies t).picture (vary X (U₀ y)) i.val W o.a Q.table Q.halo
    Brush j (η*(Φ*(hτ i))) 1 (fun y=>FullVolume.Ray.trace w (phraseS (f y))) s:=by
  intro f; let i':=i.val
  let T':= Real.exp (x₀* η) -- avoid let copy
  have ht(t:sun):0 ≤ η:= (norm_nonneg _).trans (hh 0); have hu:0 ≤ hτ i:= prosp M V D hc hp hb hA i
  by_cases he₁: Ac.Spark H.supportP i.val ∧troupe T R Q.halo (radiusB x₀) i.val ∧ V.pole.turn.badge S∈i.val
  swap; · apply Brush.zi _ (mul_nonneg (ht tip) (mul_nonneg (scentL V.pole H|>.2.1) hu)) zero_le_one
          filter_upwards with y; unfold FullVolume.Ray.trace; refine sum_eq_zero fun t _=> ?_; rw [phrased _ t]; apply smul_eq_zero.mpr (Or.inr (?_ : f y t=0))
          have h0:=U.lay t.property; have hP0:= U.troupe_hold t h0 i'; let Z:=vary X (U₀ y)
          by_cases h7: V.pole.turn.badge S∈i.val; swap; · exact stalk (V.flies t) Z (by rw [V.kind]; exact h7)
          have hH : ¬ (Ac.Spark H.supportP i.val ∧ Matter.troupe T R Q.halo B₀ i.val) := fun h=> he₁ ⟨h.1,h.2,h7⟩
          apply noPage (o:=o) Z _
          apply not_and_or.mp; rintro ⟨ha,hl⟩; rw [show Z.B=radiusB x₀ from congr_arg _ hx] at ha hl; exact hH ⟨(U.arena t h0).symm ▸ ha,hP0.2 hl⟩
  obtain ⟨hT,hK,hEp⟩:= he₁; rw [twined M V D hc hp hb hA i hEp hT]; let D':= η *(seasoned M V p (π) ν α (k+j) i')
  let A i':= (planted X i.val).taggedL i'; let g(t:S.Choices)(y:E):= FullVolume.Ray.trace w (phraseS (fun p=> fence V (A t) U₀ i' p y))
  have hF(t:S.Choices) : Brush j D' 1 (g t) s:= earnsL M V D (A t) hx he hv (planted_valid X i.val) hy hU hc hr W' Y' w η hh i' hK h hEp
  have hZ(p:sun): (fun i:E=> f i p)=ᶠ[𝓝 s] fun i=> likely (fun t=>fence V (A t) U₀ i' p i) :=by
      let P:= U.beams p (U.lay p.property); let Qo:=V.flies p; have hP : Healthy (Pressure.temp x₀) (P.unionP i') X.V:= by rw [show P.unionP i'= _ from congr_fun (U.stage _ (U.lay p.property)).symm _]; exact h
      have hr:=Qo.arcPage X i.val P hx he hv i.2.2 hP hU hy (fun a=>( (M.plot _ (U.lay p.property)).rays F (A a) hx he hv (planted_valid X i') E U₀ s hy hU).1)
      filter_upwards [hr] with y ht; apply ht.trans
      let a:=vary X (U₀ y); unfold Leaf.grove; rw [show (vary X (U₀ y)).B=B₀ from congr_arg _ hx]; -- B₀
      have hz := U.lay p.property
      rw [if_pos (show Ac.Spark (areas (U.notes p) T Q.halo (radiusB x₀)) i.val∧troupe T (U.notes p) Q.halo (radiusB x₀) i.val from ⟨(show Ac.Spark P.supportP i.val from (U.arena _ hz) ▸ hT),(U.troupe_hold _ hz i').mp hK⟩)]
      apply congr_arg likely; funext t
      have hf := Qo.casin (W:=W) (a:=o.a) (Ñ:=Q.table) X i' P hx i.2.2 hP t (U₀ y) (U₀ y) (fun _ _ _=>rfl); refine hf.symm.trans ?_
      unfold fence; rw [congr_fun (U.stage p hz) i'] <;> rfl
  apply (March.Captain.avgBrush g D' _ hF).shimmy
  filter_upwards [(eventually_all_finset w.support).2 (fun i _=> hZ i)] with x hx
  unfold FullVolume.Ray.trace; simp_rw [phrased]; unfold likely g FullVolume.Ray.trace; simp_rw [phrased,smul_eq_mul]
  rw [sum_comm (s:=univ),mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [hx i hi]; unfold likely; rw [mul_left_comm]; apply congr_arg; rw [mul_sum]
-- across cameras
lemma rocketsL (X:Config G c) (i:H.ThinP) (hx:Healthy (Pressure.temp x₀) (H.smallAt i) X) :
    let f(y:Config G c) (t:sun):= escort (V.flies t) χ Q.table i.val Q.halo T W x₀ o.K o.a y
    Ore X (fun y=>FullVolume.Ray.trace w (phraseS (f y))) u (η*(Φ*(hτ i))) j:=by
    intro f E _ _ _ A y hy hU
    letI:Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    let I:= Greenbelt.Reserve S; let F k:= Greenbelt.prism T x₀ χ o.K X (Greenbelt.allot (S:=S) k)
    let g k x (t:sun):=(V.flies t).picture (vary (F k) (A x)) i.val W o.a Q.table Q.halo
    let f k x:= FullVolume.Ray.trace w (phraseS (g k x)); let d:= η*(Φ*(hτ i))
    have hx' (i:I) : Brush j d 1 (f i) y:= tires M V D hc hr W' Y' w η hh ‹foam Q L› hb hA (F i) rfl rfl rfl hy hU _ hx -- order
    apply (March.Captain.avgBrush f d _ hx').shimmy; filter_upwards with x
    unfold FullVolume.Ray.trace; simp_rw [phrased]; unfold likely f FullVolume.Ray.trace -- first f shadowed! change wream
    simp_rw [phrased,smul_eq_mul]; rw [sum_comm (s:=univ),mul_sum]; apply Finset.sum_congr rfl; intro t _; let A:ℝ:= (Fintype.card I:ℝ)⁻¹
    change w t*(A* ∑ k:I,g k x t)= _; rw [mul_left_comm]; apply congr_arg; rw [mul_sum] -- check wrea
end Mill
end YM.ConnectedActivityE6.Empire.Imago
